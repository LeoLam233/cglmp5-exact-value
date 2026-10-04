"""Shared fail-closed JSON/schema boundary for the v0.1.1 certificate readers.

Only scalar/rational numerals accept canonical decimal strings. Words and
structural dimensions use JSON integers (never booleans or floating aliases).
See SCHEMA.md for the distinction between format policy and mathematical truth.
"""
from __future__ import annotations
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys

VERSION = 'cglmp5-strict-schema-v0.1.1'
FILES = ('SOS14.json', 'EXACT_KERNELS.json', 'EXACT_SOS_CANDIDATE.json', 'POSITIVITY_CERTIFICATE.json')
BLOCKS = [1, 6, 7, 8, 9]
SIZES = {'1': 2, '6': 4, '7': 3, '8': 3, '9': 2}
POLYNOMIAL_DESCENDING = [5, 0, -65, 0, 144, 96, 16]
SOS_DECLARATIONS = {
    'theorem': 'mu*I-B=sum_{r=1}^{14} d_r*(R_r^dagger R_r + R_r R_r^dagger)',
    'root': 'largest real root; isolated above 3',
    'relations': 'U_r^5=I; U_r unitary; even generators commute with odd generators',
    'scalar_encoding': 'index a+2*b+6*c+12*d for sqrt5^a*(5mu)^b*sqrt(10+2sqrt5)^c*i^d; positive integer common denominator',
}

class SchemaError(ValueError):
    """Malformed exact input, rejected before mathematical computation."""

class CanonicalFormatError(SchemaError):
    """Rejected packaging representation; not evidence of mathematical falsity."""


def require_normal_python():
    # Check the environment as well: -E/-I must not silently override an
    # explicitly optimization-enabled replay request.
    flag = os.environ.get('PYTHONOPTIMIZE')
    if sys.flags.optimize != 0 or (flag not in (None, '', '0')):
        raise RuntimeError('NORMAL_PYTHON_REQUIRED: reject -O, -OO and nonzero PYTHONOPTIMIZE')


require_normal_python()


def integer(value, where='integer', strings=True):
    if type(value) is int:
        return value
    if strings and type(value) is str and re.fullmatch(r'(?:0|-?[1-9][0-9]*)', value):
        return int(value)
    raise SchemaError(where + ': expected ' + ('integer or canonical decimal integer string' if strings else 'JSON integer'))


def mapping(value, where, required=()):
    if type(value) is not dict:
        raise SchemaError(where + ': expected object')
    absent = set(required) - value.keys()
    if absent:
        raise SchemaError(where + ': missing required members ' + ','.join(sorted(absent)))
    return value


def sequence(value, where, length=None):
    if type(value) is not list or (length is not None and len(value) != length):
        raise SchemaError(where + ': expected list' + (f' of length {length}' if length is not None else ''))
    return value


def scalar(value, where='scalar'):
    mapping(value, where, ('n', 'd'))
    if set(value) != {'n', 'd'}:
        raise SchemaError(where + ': scalar must have exactly n,d')
    nums = [integer(n, f'{where}.n[{j}]') for j, n in enumerate(sequence(value['n'], where+'.n', 24))]
    den = integer(value['d'], where+'.d')
    if den <= 0:
        raise SchemaError(where + ': denominator must be positive')
    return nums, den


def rational(value, where='rational'):
    mapping(value, where, ('numerator', 'denominator'))
    if set(value) != {'numerator', 'denominator'}:
        raise SchemaError(where + ': rational must have exactly numerator,denominator')
    num = integer(value['numerator'], where+'.numerator')
    den = integer(value['denominator'], where+'.denominator')
    if den <= 0:
        raise SchemaError(where + ': rational denominator must be positive')
    return num, den


def interval(value, where):
    mapping(value, where, ('lower', 'upper'))
    a,b = rational(value['lower'], where+'.lower'), rational(value['upper'], where+'.upper')
    if a[0]*b[1] > b[0]*a[1]:
        raise SchemaError(where + ': reversed rational interval')


def boxes(value, where):
    mapping(value, where, ('mu','sqrt5','u'))
    for name in ('mu','sqrt5','u'):
        interval(value[name], where+'.'+name)


def word(value, where='word', compact=False):
    factors = sequence(value, where)
    out = []
    for j,pair in enumerate(factors):
        sequence(pair, f'{where}[{j}]', 2)
        r,k = (integer(v, f'{where}[{j}][{i}]', strings=False) for i,v in enumerate(pair))
        if r not in range(4) or k not in range(1,5):
            raise SchemaError(where + ': generator must be 0..3, exponent must be 1..4')
        out.append((r,k))
    # Normal form keeps all Alice factors before Bob factors and combines
    # adjacent equal generators. This check does not commute same-party words.
    saw_bob = False
    for j,(r,k) in enumerate(out):
        if r % 2:
            saw_bob = True
        elif saw_bob:
            raise CanonicalFormatError(where + ': noncanonical party order')
        if j and out[j-1][0] == r:
            raise CanonicalFormatError(where + ': unreduced adjacent generator')
    if compact and (len(out)>2 or (len(out)==2 and not (out[0][0]%2==0 and out[1][0]%2==1))):
        raise CanonicalFormatError(where + ': compact support must be 1, A, B, or AB')
    return tuple(out)


def scalar_vector(value, where, length):
    for j,v in enumerate(sequence(value, where, length)):
        scalar(v, f'{where}[{j}]')


def scalar_matrix(value, where, rows, columns):
    for j,row in enumerate(sequence(value, where, rows)):
        scalar_vector(row, f'{where}[{j}]', columns)


def block_list(value, where):
    got=[integer(x,f'{where}[{i}]',strings=False) for i,x in enumerate(sequence(value,where,5))]
    if got != BLOCKS:
        raise SchemaError(where+': required five-block order is 1,6,7,8,9')


def polynomial(value, where):
    got=[integer(x,f'{where}[{i}]',strings=False) for i,x in enumerate(sequence(value,where,7))]
    if got != POLYNOMIAL_DESCENDING:
        raise SchemaError(where+': does not match enforced target in descending coefficient order')


def unique_object(pairs):
    out={}
    for k,v in pairs:
        if k in out:
            raise SchemaError('duplicate JSON key: '+k)
        out[k]=v
    return out


def reject_constant(token):
    raise SchemaError('nonfinite JSON token: '+token)


def finite_float(token):
    value=float(token)
    if not math.isfinite(value):
        raise SchemaError('nonfinite JSON number: '+token)
    return value


def decode(raw):
    return json.loads(raw, object_pairs_hook=unique_object, parse_constant=reject_constant, parse_float=finite_float)


def _walk(value, where, counts):
    """Validate all redundant scalar/fraction/word records as exact syntax too."""
    if type(value) is dict:
        if 'n' in value or 'd' in value:
            scalar(value,where);counts['valid_integer_scalars']+=1
        if 'numerator' in value or 'denominator' in value:
            rational(value,where);counts['rational_endpoints']+=1
        if 'word' in value:
            word(value['word'],where+'.word');counts['polynomial_words']+=1
        for k,v in value.items():
            _walk(v,where+'.'+k,counts)
    elif type(value) is list:
        for j,v in enumerate(value):
            _walk(v,f'{where}[{j}]',counts)
    elif type(value) is float and not math.isfinite(value):
        raise SchemaError(where+': nonfinite number')


# These are enforced/consumed fields. All remaining top-level fields are
# historical annotations. Nested non-authoritative fields are listed in SCHEMA.
REQUIRED = {
    'SOS14.json': ('theorem','mu_polynomial','root','relations','scalar_encoding','embedding_boxes','gamma','terms'),
    'EXACT_KERNELS.json': ('blocks','Q','gamma','kernels'),
    'EXACT_SOS_CANDIDATE.json': ('target','mu_polynomial','blocks','H'),
    'POSITIVITY_CERTIFICATE.json': ('embedding_boxes','blocks'),
}


def validate_data(data, name):
    require_normal_python()
    if name not in REQUIRED:
        raise SchemaError('unsupported certificate filename: '+name)
    mapping(data,name,REQUIRED[name])
    counts={'file':name,'valid_integer_scalars':0,'rational_endpoints':0,'polynomial_words':0,'gram_Q_words':0}
    _walk(data,name,counts)
    if name == 'SOS14.json':
        for key,expected in SOS_DECLARATIONS.items():
            if type(data[key]) is not str or data[key] != expected:
                raise SchemaError(name+'.'+key+': differs from enforced target declaration')
        polynomial(data['mu_polynomial'],name+'.mu_polynomial')
        boxes(data['embedding_boxes'],name+'.embedding_boxes')
        scalar_vector(data['gamma'],name+'.gamma',5)
        ids=set()
        for i,t in enumerate(sequence(data['terms'],name+'.terms',14)):
            where=f'{name}.terms[{i}]';mapping(t,where,('id','weight','polynomial'))
            if type(t['id']) is not str or not t['id']:
                raise SchemaError(where+'.id: expected nonempty diagnostic string')
            if t['id'] in ids:
                raise CanonicalFormatError(where+'.id: duplicate diagnostic ID (traceability policy)')
            ids.add(t['id']);scalar(t['weight'],where+'.weight')
            seen=set()
            for j,term in enumerate(sequence(t['polynomial'],where+'.polynomial')):
                tw=f'{where}.polynomial[{j}]';mapping(term,tw,('word','coefficient'))
                w=word(term['word'],tw+'.word',compact=True)
                if w in seen:
                    raise CanonicalFormatError(tw+': duplicate polynomial word (canonical collection policy)')
                seen.add(w);scalar(term['coefficient'],tw+'.coefficient')
    elif name == 'EXACT_KERNELS.json':
        block_list(data['blocks'],name+'.blocks')
        for j,w in enumerate(sequence(data['Q'],name+'.Q',81)):
            word(w,f'{name}.Q[{j}]',compact=True)
        counts['gram_Q_words']=81
        if 'words' in data:
            for j,w in enumerate(sequence(data['words'],name+'.words')):
                word(w,f'{name}.words[{j}]')
        scalar_vector(data['gamma'],name+'.gamma',5)
        mapping(data['kernels'],name+'.kernels',SIZES)
        if set(data['kernels']) != set(SIZES):
            raise SchemaError(name+'.kernels: unexpected block keys')
        for key,size in SIZES.items():
            where=name+'.kernels.'+key;mapping(data['kernels'][key],where,('E',))
            scalar_matrix(data['kernels'][key]['E'],where+'.E',81,size)
    elif name == 'EXACT_SOS_CANDIDATE.json':
        if data['target'] != 'CGLMP5':
            raise SchemaError(name+'.target: does not match enforced CGLMP5 target')
        polynomial(data['mu_polynomial'],name+'.mu_polynomial')
        block_list(data['blocks'],name+'.blocks')
        mapping(data['H'],name+'.H',SIZES)
        if set(data['H']) != set(SIZES):
            raise SchemaError(name+'.H: unexpected block keys')
        for key,size in SIZES.items():
            scalar_matrix(data['H'][key],name+'.H.'+key,size,size)
    else:
        boxes(data['embedding_boxes'],name+'.embedding_boxes')
        mapping(data['blocks'],name+'.blocks',SIZES)
        if set(data['blocks']) != set(SIZES):
            raise SchemaError(name+'.blocks: unexpected block keys')
        for key,size in SIZES.items():
            where=name+'.blocks.'+key;mapping(data['blocks'][key],where,('L','D'))
            scalar_matrix(data['blocks'][key]['L'],where+'.L',size,size)
            scalar_vector(data['blocks'][key]['D'],where+'.D',size)
    counts['unverified_top_level_annotations']=sorted(set(data)-set(REQUIRED[name]))
    return counts


def load_document(path):
    path=Path(path)
    raw=path.read_bytes()
    data=decode(raw)
    report=validate_data(data,path.name)
    report.update({'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'resolved_path':str(path.resolve())})
    return data,report


def check(path):
    return load_document(path)[1]

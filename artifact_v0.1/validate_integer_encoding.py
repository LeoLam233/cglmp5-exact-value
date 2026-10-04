"""Strict serialized-integer preflight for the frozen C001 certificate files.

Addresses ALG-01 without modifying the original mathematical verifiers.
This checks syntax only; it does not establish an SOS identity or positivity.
"""
from pathlib import Path
import argparse,json,re

FILES=('SOS14.json','EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json')

def integer(value,where):
    if type(value) is int:return value
    if type(value) is str and re.fullmatch(r'-?[0-9]+',value):return int(value)
    raise ValueError(where+': expected integer or integer string')

def unique_object(pairs):
    out={}
    for k,v in pairs:
        if k in out:raise ValueError('duplicate JSON key: '+k)
        out[k]=v
    return out

def check(path):
    data=json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=unique_object)
    scalars=0;fractions=0;words=0
    def walk(obj,where):
        nonlocal scalars,fractions,words
        if isinstance(obj,dict):
            if 'n' in obj and 'd' in obj:
                ns=obj['n']
                if not isinstance(ns,list) or len(ns)!=24:raise ValueError(where+': expected 24 scalar numerators')
                for j,n in enumerate(ns):integer(n,f'{where}.n[{j}]')
                if integer(obj['d'],where+'.d')<=0:raise ValueError(where+': denominator must be positive')
                scalars+=1
            if 'numerator' in obj and 'denominator' in obj:
                integer(obj['numerator'],where+'.numerator')
                if integer(obj['denominator'],where+'.denominator')<=0:raise ValueError(where+': rational denominator must be positive')
                fractions+=1
            if 'word' in obj:
                w=obj['word']
                if not isinstance(w,list):raise ValueError(where+': word must be a list')
                for j,pair in enumerate(w):
                    if not isinstance(pair,list) or len(pair)!=2:raise ValueError(where+': word factor must be [r,k]')
                    r=integer(pair[0],f'{where}.word[{j}].r');k=integer(pair[1],f'{where}.word[{j}].k')
                    if r not in range(4) or k not in range(1,5):raise ValueError(where+': invalid generator/exponent')
                words+=1
            for k,v in obj.items():walk(v,where+'.'+k)
        elif isinstance(obj,list):
            for j,v in enumerate(obj):walk(v,f'{where}[{j}]')
    walk(data,path.name)
    if not scalars:raise ValueError(path.name+': no serialized scalars')
    return {'file':path.name,'valid_integer_scalars':scalars,'rational_endpoints':fractions,'polynomial_words':words}

def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    a.add_argument('--output',type=Path)
    x=a.parse_args();rows=[check(x.root/n) for n in FILES]
    out={'status':'PASS','scope':'strict encoding preflight only; no mathematical certification','files':rows,'total_integer_scalars':sum(r['valid_integer_scalars'] for r in rows)}
    print(json.dumps(out,indent=2))
    if x.output:x.output.write_text(json.dumps(out,indent=2),encoding='utf-8')

if __name__=='__main__':main()

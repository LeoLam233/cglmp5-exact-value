#!/usr/bin/env python3
"""Generate canonical typed Int/Nat data, then lossless source-fragment proofs."""
import argparse, sys
if sys.flags.optimize:
    raise SystemExit('Refusing optimized Python: generator assertions must remain enabled')
_parser = argparse.ArgumentParser(description=__doc__)
_parser.add_argument('--check', action='store_true', help='Compare outputs without writing any file')
_check = _parser.parse_args().check
def emit(path, text):
    if _check:
        if not path.is_file() or path.read_text() != text:
            raise SystemExit('Generated output mismatch: ' + str(path))
    else:
        path.write_text(text)
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'artifact_v0.1.1/SOS14.json'
EXPECTED='1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2'
b=SOURCE.read_bytes()
if hashlib.sha256(b).hexdigest()!=EXPECTED: raise ValueError('canonical source hash mismatch')
s=b.decode('utf8');data=json.loads(s)
assert s == json.dumps(data,indent=2)
OUT=ROOT/'lean/CGLMP5'
if not _check: OUT.mkdir(parents=True,exist_ok=True)
def q(s):return json.dumps(str(s),ensure_ascii=False)
def ls(xs):return '['+', '.join(xs)+']'
def scalar(a):return '⟨'+ls(str(int(x)) for x in a['n'])+', '+str(int(a['d']))+'⟩'
def coeff(a):return '⟨'+ls('('+str(x)+', '+str(k)+')' for x,k in a['word'])+', '+scalar(a['coefficient'])+'⟩'
def term(a):return '⟨'+q(a['id'])+', '+scalar(a['weight'])+', [\n  '+',\n  '.join(coeff(c) for c in a['polynomial'])+'\n]⟩'
def rational(v):return '⟨'+str(int(v['numerator']))+', '+str(int(v['denominator']))+'⟩'
def box(v):return '⟨'+rational(v['lower'])+', '+rational(v['upper'])+'⟩'
def render_at(v,n):
 rows=json.dumps(v,indent=2).splitlines();return '\n'.join(rows[:1]+[' '*n+l for l in rows[1:]])
def header(imports):return '\n'.join('import CGLMP5.'+x for x in imports)+'\n\nnamespace CGLMP5.CertificateSource\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n'
def save(name,body): emit(OUT/(name+'.lean'),body+'\nend CGLMP5.CertificateSource\n')
for j,t in enumerate(data['terms']):
 name=f'CertificateTerm{j:02}'
 body=header(['CertificateSyntax'])+f'def term{j:02} : RawTerm := {term(t)}\n\n'
 body+=f'theorem term{j:02}_valid : term{j:02}.valid := by decide\n'
 save(name+'Data',body)
emb=header(['CertificateSyntax'])
for key,name in [('mu','muBox'),('sqrt5','sBox'),('u','uBox')]:emb+='def '+name+' : RawBox := '+box(data['embedding_boxes'][key])+'\n'
emb+='\ndef gammaRaw : List RawScalar := '+ls(scalar(v) for v in data['gamma'])+'\n'
emb+='theorem gamma_valid : ∀ g ∈ gammaRaw, g.valid := by decide\n'
emb+='theorem box_denominators_positive : 0 < muBox.lower.denominator ∧ 0 < muBox.upper.denominator ∧ 0 < sBox.lower.denominator ∧ 0 < sBox.upper.denominator ∧ 0 < uBox.lower.denominator ∧ 0 < uBox.upper.denominator := by decide\n'
save('CertificateEmbeddingData',emb)
body=header([f'CertificateTerm{j:02}Data' for j in range(14)]+['CertificateEmbeddingData'])
body+='def rawTerms : List RawTerm := '+ls(f'term{j:02}' for j in range(14))+'\n\n'
body+='theorem rawTerms_length : rawTerms.length = 14 := by decide\n\n'
body+='theorem rawTerms_valid : ∀ t ∈ rawTerms, t.valid := by\n  simp only [rawTerms, List.mem_cons, List.not_mem_nil, or_false]\n  intro t ht\n  rcases ht with '+ ' | '.join(f'h{j}' for j in range(14))+'\n'
for j in range(14):body+=f'  · subst t; exact term{j:02}_valid\n'
save('CertificateData',body)
# The source fragment generator never contributes an unproved mathematical premise.
# Its emitted numeral decoding and all finite scientific equalities are kernel checked.
import subprocess,sys
subprocess.run([sys.executable,str(ROOT/'scripts/generate_lean_certificate_header.py')]+(['--check'] if _check else []),check=True)
subprocess.run([sys.executable,str(ROOT/'scripts/generate_lean_source_chunks.py')]+(['--check'] if _check else []),check=True)
subprocess.run([sys.executable,str(ROOT/'scripts/check_source_chunks.py')]+(['--check-only'] if _check else []),check=True)
print('Verified unchanged generated outputs from' if _check else 'Generated typed data and kernel-visible source fragments from',len(b),'canonical bytes')

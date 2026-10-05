#!/usr/bin/env python3
"""Independent readback of actual Lean source-string fragments against canonical bytes.
No theorem is established by this check: Lean independently decodes these fragments,
then verifies the polynomial identity/positivity. This binds the intended source.
"""
import sys
if sys.flags.optimize:
    raise SystemExit('Refusing optimized Python: source-authentication assertions must remain enabled')
from pathlib import Path
import hashlib,json,re,ast,argparse
root=Path(__file__).resolve().parents[1];out=root/'lean/CGLMP5'
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=root/'lean/SOURCE_CHUNKS_READBACK.json');ap.add_argument('--check-only',action='store_true',help='Read and verify without writing a receipt');args=ap.parse_args()
b=(root/'artifact_v0.1.1/SOS14.json').read_bytes(); expected='1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2';assert hashlib.sha256(b).hexdigest()==expected
D=json.loads(b);rebuilt=json.loads(b);bindings=[]
for j,t in enumerate(D['terms']):
 path=out/f'CertificateChunkData{j:02}.lean';text=path.read_text();decoded={}
 for m in re.finditer(r'def chunkScalar(\d\d(?:W|C\d\d)) : ChunkScalar := (.+)',text):
  literals=[]
  for c in re.finditer(r'⟨(true|false), (\[(?:"[0-9]+"(?:, )?)+\])⟩',m[2]):
   parts=json.loads(c[2]);assert all(1<=len(p)<=9 and p.isascii() and p.isdigit() for p in parts)
   literals.append(('-' if c[1]=='true' else '')+''.join(parts))
  assert len(literals)==25,(m[1],len(literals));decoded[m[1]]={'n':literals[:24],'d':literals[24]}
 assert decoded[f'{j:02}W']==t['weight'];rebuilt['terms'][j]['weight']=decoded[f'{j:02}W']
 term=re.search(r'def chunkTerm\d\d : ChunkTerm := ⟨("(?:[^"\\]|\\.)*"), chunkScalar\d\dW, \[\n(.*?)\n\]⟩',text,re.S);assert term;assert json.loads(term[1])==t['id']
 words=re.findall(r'⟨(\[(?:\(\d+,\d+\)(?:, )?)*\]), chunkScalar\d\dC(\d\d)⟩',term[2]);assert len(words)==len(t['polynomial'])
 for k,(wordstr,idx) in enumerate(words):
  assert int(idx)==k;word=[list(p) for p in ast.literal_eval(wordstr)];assert word==t['polynomial'][k]['word'];assert decoded[f'{j:02}C{k:02}']==t['polynomial'][k]['coefficient'];rebuilt['terms'][j]['polynomial'][k]={'word':word,'coefficient':decoded[f'{j:02}C{k:02}']}
 bindings.append({'file':path.relative_to(root).as_posix(),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'scalar_bindings':len(decoded),'word_bindings':len(words)})
# Independently read every numeric header fragment as well as the terms.
header=(out/'CertificateHeaderData.lean').read_text()
def numbers(fragment):
 vals=[]
 for c in re.finditer(r'⟨(true|false), (\[(?:"[0-9]+"(?:, )?)+\])⟩',fragment):
  parts=json.loads(c[2]);assert all(1<=len(p)<=9 and p.isascii() and p.isdigit() for p in parts)
  vals.append(('-' if c[1]=='true' else '')+''.join(parts))
 return vals
gamma_fragment=re.search(r'def sourceHeaderGamma : List ChunkScalar := (.*?)\n\ndef sourceHeaderMuBox',header,re.S)[1]
gn=numbers(gamma_fragment);assert len(gn)==125
rebuilt['gamma']=[{'n':gn[25*i:25*i+24],'d':gn[25*i+24]} for i in range(5)]
assert rebuilt['gamma']==D['gamma']
for name,key in [('Mu','mu'),('S','sqrt5'),('U','u')]:
 fragment=re.search(r'def sourceHeader'+name+r'Box : ChunkBox := (.+)',header)[1];vals=numbers(fragment);assert len(vals)==4
 rebuilt['embedding_boxes'][key]={'lower':{'numerator':vals[0],'denominator':vals[1]},'upper':{'numerator':vals[2],'denominator':vals[3]}}
 assert rebuilt['embedding_boxes'][key]==D['embedding_boxes'][key]
metadata_lines=json.loads(re.search(r'def canonicalMetadataLines : List String := (.*?)\n\ndef canonicalMetadataPrefix',header,re.S)[1]);prefix='\n'.join(metadata_lines)+'\n';assert prefix==b.decode()[:b.decode().index('  "embedding_boxes": ')]
source=(out/'CertificateSource.lean').read_text();assert 'def canonicalPrefix : String := canonicalHeaderPrefix' in source
bindings.append({'file':'lean/CGLMP5/CertificateHeaderData.lean','sha256':hashlib.sha256((out/'CertificateHeaderData.lean').read_bytes()).hexdigest(),'gamma_scalars':5,'embedding_box_integer_strings':12})
rebuilt_bytes=json.dumps(rebuilt,indent=2).encode();assert rebuilt_bytes==b
receipt={'status':'PASS','canonical_sha256':expected,'reconstructed_sha256':hashlib.sha256(rebuilt_bytes).hexdigest(),'bytes':len(b),'bindings':bindings,'scope':'Actual emitted source fragments structurally read back, all164coefficient records/all14weights/all5gamma scalars/all3embedding boxes/source word labels/static metadata prefix compared exactly. Kernel decoding equality in CertificateSource.canonical_source_decode is a separate proof gate.'}
if not args.check_only:
 args.output.parent.mkdir(parents=True,exist_ok=True)
 args.output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','bytes':len(b),'sha256':expected}))

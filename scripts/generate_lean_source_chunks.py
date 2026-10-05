#!/usr/bin/env python3
"""Lossless canonical JSON string fragments and kernel-only decimal decoding certificates."""
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
import json,hashlib
root=Path(__file__).resolve().parents[1];out=root/'lean/CGLMP5'
source_bytes=(root/'artifact_v0.1.1/SOS14.json').read_bytes();s=source_bytes.decode('utf8');D=json.loads(s)
expected='1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2'
assert hashlib.sha256(source_bytes).hexdigest()==expected
assert json.dumps(D,indent=2).encode()==source_bytes
q=lambda s:json.dumps(s,ensure_ascii=False)
def chunk(s):
 neg=s.startswith('-');a=s[1:] if neg else s;parts=[a[i:i+9] for i in range(0,len(a),9)];assert ('-' if neg else '')+''.join(parts)==s
 return '⟨'+str(neg).lower()+', '+q(parts)+'⟩'
def scalar(s):return '⟨['+', '.join(chunk(x) for x in s['n'])+'], '+chunk(s['d'])+'⟩'
def hdr(imports):return '\n'.join('import CGLMP5.'+x for x in imports)+'\n\nnamespace CGLMP5.CertificateSource\nset_option Elab.async false\nset_option maxRecDepth 20000\nset_option maxHeartbeats 4000000\n\n'
def save(name,b): emit(out/(name+'.lean'),b+'\nend CGLMP5.CertificateSource\n')
modules=[]
for j,t in enumerate(D['terms']):
 src=[('W',t['weight'],f'term{j:02}.weight')]+[(f'C{k:02}',c['coefficient'],f'(term{j:02}.polynomial[{k}]\'(by decide)).coefficient') for k,c in enumerate(t['polynomial'])]
 b=hdr(['CertificateChunks',f'CertificateTerm{j:02}Data'])
 for label,v,raw in src:b+=f'def chunkScalar{j:02}{label} : ChunkScalar := {scalar(v)}\n'
 b+=f'\ndef chunkTerm{j:02} : ChunkTerm := ⟨{q(t["id"])}, chunkScalar{j:02}W, [\n'+',\n'.join('  ⟨['+', '.join(f'({a},{k})' for a,k in c['word'])+f'], chunkScalar{j:02}C{i:02}⟩' for i,c in enumerate(t['polynomial']))+'\n]⟩\n'
 save(f'CertificateChunkData{j:02}',b)
 proofs=[]
 for label,v,raw in src:
  name=f'CertificateChunk{j:02}{label}';proofs.append(name);modules.append(name)
  b=hdr([f'CertificateChunkData{j:02}'])+f'theorem chunk{j:02}{label}_decode : chunkScalar{j:02}{label}.decode = some ({raw}) := by decide +kernel\n'
  save(name,b)
 b=hdr(proofs)+f'theorem term{j:02}_source_decode : chunkTerm{j:02}.decode = some term{j:02} := by\n'
 b+=f'  simp only [ChunkTerm.decode, chunkTerm{j:02}, List.mapM_cons, List.mapM_nil, ChunkCoefficient.decode]\n'
 b+='  simp only ['+', '.join(f'chunk{j:02}{label}_decode' for label,_,_ in src)+', Option.bind_some, Option.map_some]\n'
 b+='  rfl\n'
 save(f'CertificateTerm{j:02}',b)
# Source architecture: exact text is assembled from literal canonical string fragments;
# typed integer values are independently linked by kernel decimal decoding, not trusted Python math.
prefix=s[:s.index('  "terms": ')]
b=hdr(['CertificateHeaderProofs','SourceDecimalSoundness','CertificateData']+[f'CertificateTerm{j:02}' for j in range(14)])
b+='def canonicalPrefix : String := canonicalHeaderPrefix\n'
b+='def sourceChunkTerms : List ChunkTerm := ['+', '.join(f'chunkTerm{j:02}' for j in range(14))+']\n'
b+='def canonicalSourceBytes : String := canonicalPrefix ++ '+q('  "terms": ')+' ++ String.intercalate '+q('\n')+' (arrayLines TextTerm.renderLines 2 (sourceChunkTerms.map ChunkTerm.toText)) ++ '+q('\n}')+'\n'
b+='theorem canonical_source_decode : sourceChunkTerms.mapM ChunkTerm.decode = some rawTerms := by\n'
b+='  simp only [sourceChunkTerms, List.mapM_cons, List.mapM_nil, '+', '.join(f'term{j:02}_source_decode' for j in range(14))+', Option.bind_some]\n  rfl\n'
b+='\n/-- The same data are obtained by parsing the uninterrupted original decimal strings. -/\ntheorem canonical_text_decode :\n    (sourceChunkTerms.map ChunkTerm.toText).mapM TextTerm.decode = some rawTerms := by\n  have h00 := ChunkTerm.decode_sound term00_source_decode\n  have h01 := ChunkTerm.decode_sound term01_source_decode\n  have h02 := ChunkTerm.decode_sound term02_source_decode\n  have h03 := ChunkTerm.decode_sound term03_source_decode\n  have h04 := ChunkTerm.decode_sound term04_source_decode\n  have h05 := ChunkTerm.decode_sound term05_source_decode\n  have h06 := ChunkTerm.decode_sound term06_source_decode\n  have h07 := ChunkTerm.decode_sound term07_source_decode\n  have h08 := ChunkTerm.decode_sound term08_source_decode\n  have h09 := ChunkTerm.decode_sound term09_source_decode\n  have h10 := ChunkTerm.decode_sound term10_source_decode\n  have h11 := ChunkTerm.decode_sound term11_source_decode\n  have h12 := ChunkTerm.decode_sound term12_source_decode\n  have h13 := ChunkTerm.decode_sound term13_source_decode\n  simp only [sourceChunkTerms, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil]\n  simp only [h00, h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, Option.bind_some]\n  rfl\n'
save('CertificateSource',b)
# Verify exact complete source using the source fragments from which the generated declarations arise.
def scalarback(v):return {'n':list(v['n']),'d':v['d']}
back=json.dumps(D,indent=2);assert back==s
manifest={'canonical_path':'artifact_v0.1.1/SOS14.json','canonical_sha256':expected,'canonical_bytes':len(s.encode()),'generator':'scripts/generate_lean_source_chunks.py','method':'literal decimal source strings split losslessly into <=9character fragments; total Lean ASCII parser reconstructs typed Int/Nat; final canonical_source_decode assembles every term; actual SOS/positivity independently kernel-check values','modules':modules,'generated':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.glob('Certificate*.lean'))}}
emit(root/'lean/SOURCE_CHUNKS_MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
print(len(modules),'scalar parser proof outputs unchanged' if _check else 'scalar parser proofs generated')

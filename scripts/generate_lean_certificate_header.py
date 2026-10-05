#!/usr/bin/env python3
"""Generate lossless header syntax; Lean proves all numeric decoding obligations."""
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
import json, hashlib
root=Path(__file__).resolve().parents[1]
out=root/'lean/CGLMP5'
src=root/'artifact_v0.1.1/SOS14.json'
raw=src.read_bytes(); text=raw.decode(); data=json.loads(text)
expected='1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2'
assert hashlib.sha256(raw).hexdigest()==expected
assert json.dumps(data,indent=2).encode()==raw
q=lambda x:json.dumps(x,ensure_ascii=False)
def chunk(s):
 neg=s.startswith('-'); digits=s[1:] if neg else s
 assert digits and digits.isascii() and digits.isdecimal()
 parts=[digits[i:i+9] for i in range(0,len(digits),9)]
 assert ('-' if neg else '')+''.join(parts)==s
 return f'⟨{str(neg).lower()}, {q(parts)}⟩'
def scalar(s):return '⟨['+', '.join(map(chunk,s['n']))+'], '+chunk(s['d'])+'⟩'
def rat(r):return '⟨'+chunk(r['numerator'])+', '+chunk(r['denominator'])+'⟩'
def box(b):return '⟨'+rat(b['lower'])+', '+rat(b['upper'])+'⟩'
b='import CGLMP5.CertificateHeaderSyntax\nimport CGLMP5.CertificateEmbeddingData\n\nnamespace CGLMP5.CertificateSource\n\n'
b+='def sourceHeaderGamma : List ChunkScalar := ['+',\n  '.join(map(scalar,data['gamma']))+']\n\n'
for name,key in [('Mu','mu'),('S','sqrt5'),('U','u')]:b+=f'def sourceHeader{name}Box : ChunkBox := '+box(data['embedding_boxes'][key])+'\n\n'
b+='def canonicalMetadataLines : List String := '+q(text[:text.index('  "embedding_boxes": ')].splitlines())+'\n\n'
b+='def canonicalMetadataPrefix : String := String.intercalate '+q('\n')+' canonicalMetadataLines ++ '+q('\n')+'\n\n'
b+='''/-- Every numeric header string is rendered from the same chunks whose decoding is checked. -/
def sourceHeaderNumericLines : List String :=
  prefixLine "  \\"embedding_boxes\\": " (suffixLine "," (textBoxesLines
    sourceHeaderMuBox.toText sourceHeaderSBox.toText sourceHeaderUBox.toText)) ++
  prefixLine "  \\"gamma\\": " (suffixLine ","
    (arrayLines TextScalar.renderLines 2 (sourceHeaderGamma.map ChunkScalar.toText)))

def headerLines : List String := canonicalMetadataLines ++ sourceHeaderNumericLines

def canonicalHeaderPrefix : String :=
  String.intercalate "\\n" headerLines ++ "\\n"

end CGLMP5.CertificateSource
'''
emit(out/'CertificateHeaderData.lean',b)
p='import CGLMP5.CertificateHeaderData\n\nnamespace CGLMP5.CertificateSource\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 20000\n\n'
p+='theorem header_gamma_decode : sourceHeaderGamma.mapM ChunkScalar.decode = some gammaRaw := by\n  decide +kernel\n\n'
for name,rawname in [('Mu','mu'),('S','s'),('U','u')]:
 p+=f'theorem header_{rawname}_box_decode : sourceHeader{name}Box.decode = some {rawname}Box := by\n  decide +kernel\n\n'
p+='''theorem header_gamma_text_decode :
    (sourceHeaderGamma.map ChunkScalar.toText).mapM TextScalar.decode = some gammaRaw := by
  simpa only [List.mapM_map, Function.comp_def] using
    option_mapM_sound ChunkScalar.decode (fun s => s.toText.decode)
      (fun s r h => ChunkScalar.decode_sound h) sourceHeaderGamma gammaRaw header_gamma_decode

'''
for name,rawname in [('Mu','mu'),('S','s'),('U','u')]:
 p+=f'theorem header_{rawname}_box_text_decode : sourceHeader{name}Box.toText.decode = some {rawname}Box :=\n  ChunkBox.decode_sound header_{rawname}_box_decode\n\n'
p+='end CGLMP5.CertificateSource\n'
emit(out/'CertificateHeaderProofs.lean',p)
manifest={'canonical_path':str(src.relative_to(root)),'canonical_sha256':expected,'canonical_bytes':len(raw),'numeric_fields':{'gamma_scalars':5,'embedding_boxes':3,'endpoint_decimal_strings':12},'method':'lossless <=9 digit fragments; kernel parser checks exact values; generic soundness proves uninterrupted decimal text semantics','generated':{name:hashlib.sha256((out/name).read_bytes()).hexdigest() for name in ['CertificateHeaderData.lean','CertificateHeaderProofs.lean']}}
emit(root/'lean/SOURCE_HEADER_MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
print('Verified unchanged canonical header outputs.' if _check else 'Generated lossless canonical header data and kernel proof obligations.')

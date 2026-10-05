#!/usr/bin/env python3
"""Read back the actual Lean-defined source text and compare canonical bytes.
This executable IO comparison authenticates inputs; it does not discharge a proof.
"""
from pathlib import Path
import subprocess,hashlib,json,datetime,argparse
root=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=root/'lean/LEAN_SOURCE_BYTES_READBACK.json');args=ap.parse_args()
r=subprocess.run(['lake','env','lean','--run','../verification/lean/ReadSourceBytes.lean'],cwd=root/'lean',stdout=subprocess.PIPE,stderr=subprocess.PIPE)
expected=(root/'artifact_v0.1.1/SOS14.json').read_bytes()
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':r.returncode,'actual_bytes':len(r.stdout),'expected_bytes':len(expected),'actual_sha256':hashlib.sha256(r.stdout).hexdigest(),'expected_sha256':hashlib.sha256(expected).hexdigest(),'stderr':r.stderr.decode(errors='replace'),'status':'PASS' if r.returncode==0 and r.stdout==expected else 'FAIL','scope':'Actual evaluated canonicalSourceBytes exact readback. Separate kernel theorem canonical_source_decode and scientific proof are mandatory.'}
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));raise SystemExit(0 if receipt['status']=='PASS' else 1)

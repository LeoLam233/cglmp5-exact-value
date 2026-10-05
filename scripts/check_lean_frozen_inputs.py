#!/usr/bin/env python3
"""Verify immutable v0.1.1 science and the separately pinned current-paper editorial update."""
import sys
if sys.flags.optimize:
    raise SystemExit('Refusing optimized Python: source-authentication assertions must remain enabled')
from pathlib import Path
import argparse, hashlib, json, subprocess
root=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--output',required=True,type=Path);ap.add_argument('--remote',action='store_true');a=ap.parse_args()
def git(*xs):return subprocess.check_output(['git',*xs],cwd=root,text=True).strip()
def blob(ref,path):return subprocess.check_output(['git','show',ref+':'+path],cwd=root)
tag='54dc6cabee9b272dd35da736ef9a2208fc715bb8';commit='73b99dd22af68bd7a10927124d0b4ea7d6e8b78f'
assert git('rev-parse','v0.1.1')==tag and git('rev-parse','v0.1.1^{}')==commit and git('cat-file','-t','v0.1.1')=='tag'
protected=['artifact_v0.1','artifact_v0.1.1','docs/LEAN_HANDOFF.md']
assert not git('diff','v0.1.1','--',*protected)
expected={'SOS14.json':'1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2','EXACT_KERNELS.json':'6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5','EXACT_SOS_CANDIDATE.json':'14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649','POSITIVITY_CERTIFICATE.json':'22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de'}
for name,h in expected.items():
 for v in ['artifact_v0.1','artifact_v0.1.1']:assert hashlib.sha256((root/v/name).read_bytes()).hexdigest()==h
# Preserve the user's concurrent current-main prior-work attribution without changing
# the scientific baseline or silently reverting that separately published maintenance.
editorial='1e3282749c9fce2163aaeb8415d8936db88d43ad'
assert git('rev-parse',editorial+'^{tree}')=='f65a6470f6ec9f8f3c4e15086f76e5df0fe0de46'
assert not git('diff',editorial,'--','paper')
old=blob(commit,'paper/main.tex');current=(root/'paper/main.tex').read_bytes()
before=b'nonmaximally entangled states have a substantial history. Zohren and Gill'
after=b'''nonmaximally entangled states have a substantial history. Ac\\'in, Durt,
Gisin, and Latorre \\cite{AcinDurtGisinLatorre} showed that nonmaximally
entangled states give larger CGLMP violations than maximally entangled
states with these measurements. Their Bell-operator calculation already
reports $3.0157$ for $d=5$ in Table~I; it does not supply the unrestricted
quantum upper-bound certificate proved here. Zohren and Gill'''
assert old.count(before)==1 and old.replace(before,after,1)==current
paper_paths=git('ls-files','--','paper').splitlines()
paper_hashes={name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in paper_paths}
remote=None
if a.remote:
 remote=git('ls-remote','origin','refs/tags/v0.1.1','refs/tags/v0.1.1^{}');assert tag+'\trefs/tags/v0.1.1' in remote and commit+'\trefs/tags/v0.1.1^{}' in remote
receipt={'status':'PASS','annotated_tag':tag,'peeled_commit':commit,'canonical_json':expected,'unchanged_paths':protected,'remote_refs':remote,'current_paper_editorial_commit':editorial,'current_paper_sha256':paper_hashes,'canonical_main_tex_sha256':hashlib.sha256(old).hexdigest(),'only_main_tex_delta':'Exact pinned prior-work attribution paragraph; every other TeX byte unchanged','scientific_target_changed':False,'editorial_integration_record':'docs/CURRENT_MAIN_EDITORIAL_INTEGRATION.json'}
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

#!/usr/bin/env python3
"""R01 layered manifests with explicit historical and current base directories."""
import argparse, hashlib, json, subprocess, zipfile
from pathlib import Path, PurePosixPath
EXPECTED_ARCHIVE='12e2864ed19d99500b72d4aefe6e2b27939fb67c05aa355b38b997456a55fc43'
def digest(b):return hashlib.sha256(b).hexdigest()
def sha(p):return digest(p.read_bytes())
def require(v,s):
    if not v:raise RuntimeError(s)
def lines(text):
    for line in text.splitlines():
        if line.strip() and not line.lstrip().startswith('#'):
            h,n=line.split(None,1);yield h,n.strip().lstrip('*').removeprefix('./')
def manifest_file(path,base):
    rows=[]
    for h,n in lines(path.read_text()):
        p=base/n;got=sha(p);require(got==h,'manifest mismatch '+str(p));rows.append({'path':n,'sha256':got})
    return {'manifest':str(path),'manifest_sha256':sha(path),'base_directory':str(base),'checked':len(rows),'entries':rows,'status':'PASS'}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--archive',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--source-manifest',action='store_true');a=ap.parse_args();a.root=a.root.resolve();a.archive=a.archive.resolve();require(sha(a.archive)==EXPECTED_ARCHIVE,'wrong Phase-B archive')
    rows=[]
    with zipfile.ZipFile(a.archive) as z:
        require(z.testzip() is None,'archive CRC failure');snapshot=json.loads(z.read('CHECKPOINT_SNAPSHOT_MANIFEST.json'))
        for r in snapshot['files']:require(digest(z.read(r['path']))==r['sha256'],'snapshot mismatch '+r['path'])
        rows.append({'scope':'outer Phase-B final-complete immutable snapshot','status':'PASS','archive_sha256':sha(a.archive),'snapshot_entries':len(snapshot['files'])})
        for manifest in ['outputs/OUTPUT_SHA256SUMS.txt','work/corpus/CGLMP5_PHASE_B_FINAL/CORPUS_SHA256SUMS.txt','work/corpus/CGLMP5_PHASE_B_FINAL/PACKAGE_SHA256SUMS.txt','work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/SCIENTIFIC_PAYLOAD_SHA256SUMS.txt','work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/PACKAGE_SHA256SUMS.txt']:
            base=str(PurePosixPath(manifest).parent);entries=[]
            for h,n in lines(z.read(manifest).decode()):
                member=base+'/'+n;require(digest(z.read(member))==h,'archive inner manifest mismatch '+member);entries.append({'member':member,'sha256':h})
            rows.append({'scope':'historical archive manifest; immutable base inside archive','manifest':manifest,'base_directory':base,'manifest_sha256':digest(z.read(manifest)),'entries':entries,'checked':len(entries),'status':'PASS'})
    original={}
    tracked=subprocess.check_output(['git','ls-tree','-r','--name-only','v0.1.0','--','artifact_v0.1'],cwd=a.root,text=True).splitlines()
    for n in tracked:
        b=subprocess.check_output(['git','show','v0.1.0:'+n],cwd=a.root);require(digest(b)==sha(a.root/n),'frozen tag bytes changed '+n);original[n]={'original_tag':'v0.1.0','original_sha256':digest(b),'curated_path':n,'current_sha256':sha(a.root/n)}
    rows.append({'scope':'frozen public payload manifest; base artifact_v0.1, historical unchanged','verification':manifest_file(a.root/'artifact_v0.1/MANIFEST.sha256',a.root/'artifact_v0.1')})
    rows.append({'scope':'current hardened artifact only; excludes its own manifest','verification':manifest_file(a.root/'artifact_v0.1.1/MANIFEST.sha256',a.root/'artifact_v0.1.1')})
    if a.source_manifest:rows.append({'scope':'current nonreceipt release source only; self and receipt/gate exclusions documented','verification':manifest_file(a.root/'SOURCE_MANIFEST.sha256',a.root)})
    science={}
    for n in ['SOS14.json','EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json']:
        hs={v:sha(a.root/v/n) for v in ['artifact_v0.1','artifact_v0.1.1']};require(len(set(hs.values()))==1,'science changed');science[n]=hs
    result={'status':'PASS','layers':rows,'original_to_curated_map':original,'original_frozen_files_checked':len(original),'scientific_original_to_revised':science,'historical_root_SHA256SUMS_scope':'SHA256SUMS.txt explicitly labels historical v0.1.0 ZIP asset basenames plus current paper/immutable Phase-B external asset basenames; it is not a complete repository-tree manifest. SOURCE_MANIFEST.sha256 covers current nonreceipt source and the external release-asset manifest is separate.','source_manifest_included':a.source_manifest};a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','layers':len(rows),'frozen_files':len(original),'source_manifest_included':a.source_manifest}));
if __name__=='__main__':main()

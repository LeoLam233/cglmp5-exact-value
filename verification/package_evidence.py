#!/usr/bin/env python3
"""Lossless, content-deduplicated evidence archive with a verified restore map."""
import argparse,hashlib,json,stat,zipfile
from pathlib import Path
RESTORE='''#!/usr/bin/env python3
import argparse,hashlib,json,os,zipfile
from pathlib import Path,PurePosixPath
p=argparse.ArgumentParser();p.add_argument('archive',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
if a.output.exists():raise RuntimeError('output must be new')
with zipfile.ZipFile(a.archive) as z:
 m=json.loads(z.read('FILES.json'));a.output.mkdir(parents=True)
 for r in m['files']:
  n=PurePosixPath(r['path'])
  if n.is_absolute() or '..' in n.parts:raise RuntimeError('unsafe archive path')
  b=z.read('blobs/'+r['sha256'])
  if len(b)!=r['bytes'] or hashlib.sha256(b).hexdigest()!=r['sha256']:raise RuntimeError('corrupt blob')
  q=a.output/str(n);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);q.chmod(r['mode'])
 print('Restored and hash-verified',len(m['files']),'files')
'''
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();root=a.root.resolve();out=a.output.resolve()
    if out.exists():raise RuntimeError('new archive path required; retain older attempts')
    files=[];unique={}
    for p in sorted(root.rglob('*')):
        if p.is_symlink():raise RuntimeError('symlink requires explicit handling: '+str(p))
        if not p.is_file() or '__pycache__' in p.parts:continue
        b=p.read_bytes();h=hashlib.sha256(b).hexdigest();files.append({'path':str(p.relative_to(root)),'bytes':len(b),'sha256':h,'mode':stat.S_IMODE(p.stat().st_mode)});unique.setdefault(h,p)
    manifest={'schema':'cglmp5.deduplicated-evidence.v1','original_root':str(root),'files':files,'scope':'All non-cache regular file bytes from regression work, including failed attempts, originals staged for replay, exact mutated inputs, logs and receipts; __pycache__ excluded as regenerated runtime cache.'}
    with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
        z.writestr('FILES.json',json.dumps(manifest,indent=2)+'\n');z.writestr('restore.py',RESTORE);z.writestr('README.txt','Run python restore.py ARCHIVE.zip NEW_OUTPUT_DIRECTORY to reconstruct exact bytes. All failed attempts remain historical FAIL, never recast as PASS.\n')
        for h,p in unique.items():z.write(p,'blobs/'+h)
    with zipfile.ZipFile(out) as z:
        if z.testzip() is not None:raise RuntimeError('CRC failure')
        for h in unique:
            if hashlib.sha256(z.read('blobs/'+h)).hexdigest()!=h:raise RuntimeError('blob mismatch')
    receipt={'status':'PASS','archive':str(out),'archive_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'archive_bytes':out.stat().st_size,'file_count':len(files),'unique_blobs':len(unique),'original_bytes':sum(x['bytes'] for x in files),'all_blob_hashes_verified':True,'manifest_sha256':hashlib.sha256(json.dumps(manifest,indent=2).encode()+b'\n').hexdigest()};out.with_suffix(out.suffix+'.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

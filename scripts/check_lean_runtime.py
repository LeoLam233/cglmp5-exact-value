#!/usr/bin/env python3
"""Compare an unpacked Lean runtime against every file in the official pinned archive."""
import argparse,datetime,hashlib,json,tarfile
from pathlib import Path
import zstandard
ap=argparse.ArgumentParser();ap.add_argument('--archive',required=True,type=Path);ap.add_argument('--runtime',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args()
expected='47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4'
def digest(f):return hashlib.file_digest(f,'sha256').hexdigest()
with a.archive.open('rb') as f:actual=digest(f)
if actual!=expected:raise SystemExit('Official Lean 4.34.1 archive digest mismatch')
files=[];errors=[];base=a.runtime.resolve()
with a.archive.open('rb') as f, zstandard.ZstdDecompressor().stream_reader(f) as stream, tarfile.open(fileobj=stream,mode='r|') as tar:
 for member in tar:
  parts=Path(member.name).parts
  if not parts or parts[0]!='lean-4.34.1-linux' or '..' in parts:raise RuntimeError('Unexpected archive member '+member.name)
  p=base.joinpath(*parts[1:])
  if member.isfile():
   src=tar.extractfile(member);h=digest(src)
   if not p.is_file():errors.append({'path':member.name,'error':'missing'});continue
   with p.open('rb') as local:localh=digest(local)
   if localh!=h:errors.append({'path':member.name,'error':'hash mismatch','official':h,'local':localh})
   files.append({'path':'/'.join(parts[1:]),'sha256':h,'bytes':member.size})
  elif member.issym():
   if not p.is_symlink() or p.readlink().as_posix()!=member.linkname:errors.append({'path':member.name,'error':'symlink mismatch'})
receipt={'status':'PASS' if not errors else 'FAIL','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'official_archive_sha256':actual,'runtime':str(base),'regular_files':len(files),'bytes':sum(x['bytes'] for x in files),'files':files,'errors':errors};a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','regular_files','bytes','errors']}));raise SystemExit(0 if not errors else 1)

from pathlib import Path
import hashlib,json,zipfile
base=Path(__file__).resolve().parent
source=json.loads((base/'scientific_attempt02/staging_manifest.json').read_text())
archive=Path('/workspace/scratch/e6e0818fcb8f/phase_b_20261004_0845/checkpoints/CGLMP5_PhaseB_checkpoint_20261004T092328Z_FINAL_COMPLETE.zip')
rows=[]
with zipfile.ZipFile(archive) as z:
 for lane,prefix in [('work','work/'),('scripts','outputs/INDEPENDENT_CHECKS/')]:
  for p,h in source[lane].items():
   member=prefix+p;got=hashlib.sha256(z.read(member)).hexdigest()
   if got!=h:raise RuntimeError('staged source differs from immutable archive: '+member)
   rows.append({'archive_path':member,'staged_sha256':h,'archive_sha256':got})
result={'status':'PASS','archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'checked_staged_files':len(rows),'staging_manifest_sha256':hashlib.sha256((base/'scientific_attempt02/staging_manifest.json').read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'files':rows,'scope':'Every staged non-cache work input and Phase-B script matches the immutable authoritative archive, not only a mutable extracted directory.'}
(base/'replay_source_identity.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(rows))

#!/usr/bin/env python3
"""Download and SHA-256 verify public GitHub release assets against a local map.

The expected JSON maps exact asset basenames to SHA-256. No credentials are
accepted or required. Only official API-provided public GitHub download URLs
for the fixed approved repository and tag are followed.
"""
import argparse
import hashlib
import json
import time
import urllib.request
from pathlib import Path

REPO = 'LeoLam233/cglmp5-exact-value'
TAG = 'v0.1.1'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--expected', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=True)
expected = json.loads(a.expected.read_text())
url = f'https://api.github.com/repos/{REPO}/releases/tags/{TAG}'
req = urllib.request.Request(url, headers={'Accept':'application/vnd.github+json','User-Agent':'CGLMP5-release-verifier'})
with urllib.request.urlopen(req, timeout=60) as response:
    release = json.load(response)
if release.get('draft') or release.get('prerelease') or release.get('tag_name') != TAG:
    raise SystemExit('FAIL: expected public stable v0.1.1 release')
assets = {item['name']: item for item in release['assets']}
results = []
for name, digest in expected.items():
    if Path(name).name != name or name not in assets:
        raise SystemExit('FAIL: absent or invalid expected asset '+name)
    asset = assets[name]
    target = asset['browser_download_url']
    if not target.startswith(f'https://github.com/{REPO}/releases/download/{TAG}/'):
        raise SystemExit('FAIL: unexpected asset origin '+name)
    h = hashlib.sha256()
    size = 0
    destination = a.output/name
    with urllib.request.urlopen(target, timeout=120) as response, destination.open('wb') as out:
        while chunk := response.read(1024*1024):
            out.write(chunk); h.update(chunk); size += len(chunk)
    actual = h.hexdigest()
    if actual != digest or size != asset['size']:
        raise SystemExit('FAIL: remote asset hash/size mismatch '+name)
    results.append({'name':name,'sha256':actual,'size':size,'asset_id':asset['id'],'url':target,'status':'PASS'})
result = {'status':'PASS','checked_unix_time':time.time(),'repository':REPO,'tag':TAG,'release_url':release['html_url'],'assets':results}
(a.output/'ASSET_READBACK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

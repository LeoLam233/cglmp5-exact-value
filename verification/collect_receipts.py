#!/usr/bin/env python3
"""Curate complete run receipts/logs, preserving failed attempts as failures.
Input replicas are retained in the deduplicated recovery ZIP, not duplicated here.
"""
import argparse,shutil,json,hashlib
from pathlib import Path

def copy(src,dst):dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--work',type=Path,required=True);a=ap.parse_args();dest=a.root/'verification/receipts';dest.mkdir(parents=True,exist_ok=True);copied=[]
    def take(p):
        rel=p.relative_to(a.work);q=dest/rel;copy(p,q);copied.append({'path':str(q.relative_to(a.root)),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()})
    for name in ['scientific_attempt01','scientific_attempt02']:
        for p in (a.work/name).rglob('*'):
            rel=p.relative_to(a.work/name)
            if p.is_file() and (len(rel.parts)==1 or rel.parts[0]=='runs'):take(p)
    for name in ['hardening_attempt01','hardening_attempt02']:
        for p in (a.work/name).rglob('*'):
            rel=p.relative_to(a.work/name)
            if p.is_file() and (len(rel.parts)==1 or rel.parts[0]=='guards' or any(part.endswith('.run') for part in rel.parts)):take(p)
    for name in ['orchestration_attempt01','relocation_attempt01']:
        for p in (a.work/name).rglob('*'):
            rel=p.relative_to(a.work/name)
            if p.is_file() and ('relocated release with spaces' not in rel.parts):take(p)
    for p in a.work.iterdir():
        if p.is_file() and p.suffix in ['.json','.txt','.py']:take(p)
    (dest/'COLLECTION.json').write_text(json.dumps({'status':'PASS','scope':'Exact copies of available run receipts/logs; failed attempt status preserved. Full original/staged/mutated input replicas are in deduplicated evidence archive.','files':copied},indent=2)+'\n');print(len(copied),'files curated')
if __name__=='__main__':main()

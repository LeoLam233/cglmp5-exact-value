import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--root');p.add_argument('--output',type=Path);p.add_argument('--mode');a=p.parse_args()
if a.mode != 'incomplete':
 a.output.write_text(json.dumps({'status':'FAIL' if a.mode=='false_success' else 'PASS','nonzero_residual_count':1 if a.mode=='nonzero_residual' else 0}))
print('FAIL with intentional exit0' if a.mode=='false_success' else 'fixture completed')

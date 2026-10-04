#!/usr/bin/env python3
"""Sensitivity checks using in-memory corruptions; the supplied input files remain unchanged."""
import argparse, contextlib, copy, io, json, subprocess, sys, tempfile
from pathlib import Path
import audit

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('root',type=Path)
    args=ap.parse_args();data=audit.load(args.root)
    stream=io.StringIO()
    with contextlib.redirect_stdout(stream):
        boxes,B,Q,universe=audit.basic(args.root,data)
        weights,bounds=audit.positivity(data,boxes)
    result={}
    def expect_failure(name,fn):
        try:
            with contextlib.redirect_stdout(stream):fn()
        except AssertionError as e:
            result[name]={'rejected':True,'reason':str(e)}
        else: raise RuntimeError('Negative control unexpectedly accepted: '+name)
    altered=copy.deepcopy(data)
    c=altered['sos']['terms'][0]['polynomial'][0]['coefficient']
    c['n'][0]=str(int(c['n'][0])+int(c['d']))
    expect_failure('add_one_to_first_R_coefficient',lambda:audit.sos_identity(altered,B,Q,weights))
    changed=copy.deepcopy(data)
    changed['sos']['terms'][0]['polynomial'][0]['word']=[[1,2]]
    expect_failure('change_first_U1_power_from_1_to_2',lambda:audit.sos_identity(changed,B,Q,weights))
    negative=copy.deepcopy(data)
    negative['sos']['terms'][0]['weight']['n']=[str(-int(c)) for c in negative['sos']['terms'][0]['weight']['n']]
    expect_failure('negate_first_weight',lambda:audit.positivity(negative,boxes))
    wrongB=dict(B)
    for k in range(1,5):
        w=audit.word([(3,k),(0,-k)]);wrongB[w]=wrongB[w]*audit.z**(4*k)
    expect_failure('delete_last_edge_omega_phase',lambda:audit.sos_identity(data,wrongB,Q,weights))
    with tempfile.TemporaryDirectory(prefix='cglmp5_mutation_') as td:
        root=Path(td);(root/'candidate').mkdir()
        (root/'candidate'/'SOS14.json').write_text(json.dumps(altered['sos']))
        proc=subprocess.run([sys.executable,str(Path(__file__).parent/'crosscheck.py'),str(root),'--out',str(root/'out.json')],capture_output=True,text=True)
        if proc.returncode==0 or 'AssertionError' not in proc.stderr:
            raise RuntimeError('Second checker did not fail as intended: '+proc.stderr[-1000:])
        result['second_checker_add_one_to_R']={'rejected':True,'reason':'nonzero radical-tower exact residual; AssertionError'}
    out=Path(__file__).parent/'negative_control_results.json'
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False))
    print(json.dumps(result,indent=2,ensure_ascii=False))

if __name__=='__main__':main()

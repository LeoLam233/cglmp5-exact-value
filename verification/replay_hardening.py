#!/usr/bin/env python3
"""R02–R05/R11/R13 acceptance for hardened certificate entrypoints.
Each subprocess retains stdout/stderr, exact source and input bindings, and
semantic classification. CLI rejection alone is insufficient: strict syntax
cases must identify SchemaError, and mathematical mutations ArithmeticError.
"""
import sys, os
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None,'','0'):raise SystemExit('REFUSED_OPTIMIZED_EXECUTION')
import argparse, copy, hashlib, json, shutil, subprocess, time
from pathlib import Path
FILES=['SOS14.json','EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json']
CONSUMERS={FILES[0]:['validate_integer_encoding.py','verify_sos14.py','verify_statement.py'],FILES[1]:['validate_integer_encoding.py','verify_independent.py'],FILES[2]:['validate_integer_encoding.py','verify_independent.py'],FILES[3]:['validate_integer_encoding.py','verify_independent.py']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def require(v,m):
    if not v:raise RuntimeError(m)
def scalar(x):
    if isinstance(x,dict):
        if set(x)=={'n','d'}:return x
        for v in x.values():
            r=scalar(v)
            if r is not None:return r
    if isinstance(x,list):
        for v in x:
            r=scalar(v)
            if r is not None:return r
    return None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.root=a.root.resolve();a.output=a.output.resolve();require(not a.output.exists(),'new output required');a.output.mkdir(parents=True)
    original=a.root/'artifact_v0.1.1';base=a.output/'baseline';shutil.copytree(original,base,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));raw={n:json.loads((base/n).read_text()) for n in FILES};rows=[];environment={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'};environment.pop('PYTHONOPTIMIZE',None)
    sources={p.name:sha(p) for p in base.glob('*.py')}
    def run(gate,label,file,mutator,entrypoints=None,expect='schema',extra=None,raw_transform=None):
        root=a.output/'cases'/label;shutil.copytree(base,root,ignore=shutil.ignore_patterns('*.json.receipt'))
        if file:
            data=copy.deepcopy(raw[file]);mutator(data);write(root/file,data)
            if raw_transform:(root/file).write_text(raw_transform((root/file).read_text()))
        if extra:extra(root)
        for ep in entrypoints or CONSUMERS[file]:
            log=root/(ep+'.run');log.mkdir();out=log/'result.json';cmd=[sys.executable,str(root/ep),'--root',str(root),'--output',str(out)];start=time.monotonic();p=subprocess.run(cmd,text=True,capture_output=True,env=environment,cwd=log)
            (log/'stdout.txt').write_text(p.stdout);(log/'stderr.txt').write_text(p.stderr)
            row={'gate':gate,'label':label,'entrypoint':ep,'command':cmd,'cwd':str(log),'returncode':p.returncode,'expected':expect,'source_sha256':sources,'input_sha256':{n:sha(root/n) for n in FILES},'stdout_sha256':sha(log/'stdout.txt'),'stderr_sha256':sha(log/'stderr.txt'),'elapsed_seconds':time.monotonic()-start,'status':'FAIL'}
            try:
                if expect in ['schema','canonical','mathematical']:
                    need={'schema':'SchemaError:','canonical':'CanonicalFormatError:','mathematical':'ArithmeticError:'}[expect]
                    require(p.returncode!=0,'mutation unexpectedly returned success')
                    if out.exists():
                        failed=json.loads(out.read_text());require(failed.get('status')=='FAIL' and failed.get('error_type')==need[:-1],'rejection was not intended '+expect+' invariant');row['reason']=failed['error'];row['failure_receipt']=failed
                    else:
                        require(need in p.stderr,'rejection was not intended '+expect+' invariant');row['reason']=p.stderr.strip().splitlines()[-1]
                else:
                    require(p.returncode==0 and out.exists(),'successful mathematical receipt missing');v=json.loads(out.read_text());require(v['status']=='PASS','mathematical status not PASS');row['semantic_result']=v
                    receipt=v['receipt'];require(receipt['enforced_target_sha256']==baseline_target_hash,'receipt switched theorem')
                    if expect=='annotative':require(bool(receipt.get('document_sha256')) or any(x.get('unverified_top_level_annotations') for x in receipt['inputs']),'annotations not disclosed')
                row['status']='PASS'
            except Exception as e:row['failure']=str(e)
            write(log/'receipt.json',row);rows.append(row);print(gate,label,ep,row['status'],row.get('failure',''),flush=True)
    # One fresh baseline establishes the fixed target identity for later receipts.
    baseline_cmd=[sys.executable,str(base/'verify_sos14.py'),'--root',str(base),'--output',str(a.output/'baseline_result.json')]
    bp=subprocess.run(baseline_cmd,capture_output=True,text=True,env=environment);(a.output/'baseline.stdout.txt').write_text(bp.stdout);(a.output/'baseline.stderr.txt').write_text(bp.stderr)
    require(bp.returncode==0,'baseline failed');baseline_result=json.loads((a.output/'baseline_result.json').read_text());baseline_target_hash=baseline_result['receipt']['enforced_target_sha256']
    scalar_mutations={
      'float':lambda c:c['n'].__setitem__(0,1.0),'boolean':lambda c:c['n'].__setitem__(0,True),'malformed_string':lambda c:c['n'].__setitem__(0,'1.0'),'plus_string':lambda c:c['n'].__setitem__(0,'+1'),'leading_zero':lambda c:c['n'].__setitem__(0,'01'),'NaN':lambda c:c['n'].__setitem__(0,float('nan')),'Infinity':lambda c:c['n'].__setitem__(0,float('inf')),'missing_n':lambda c:c.pop('n'),'missing_d':lambda c:c.pop('d'),'wrong_vector_length':lambda c:c['n'].pop(),'zero_denominator':lambda c:c.__setitem__('d','0'),'negative_denominator':lambda c:c.__setitem__('d','-1')}
    for name in FILES:
        for label,fun in scalar_mutations.items():run('R02',name[:-5]+'_'+label,name,lambda d,f=fun:f(scalar(d)))
        run('R02',name[:-5]+'_duplicate_key',name,lambda d:None,raw_transform=lambda s:s[:-2]+', "__duplicate__": 1, "__duplicate__": 2}\n')
    def word(data,name):return next(w for w in (data['Q'] if name==FILES[1] else [p['word'] for t in data['terms'] for p in t['polynomial']]) if w)
    for name in FILES[:2]:
        for label,value,index in [('boolean',True,0),('integral_float',0.0,0),('fractional_exponent',1.5,1),('bad_generator',4,0),('bad_exponent',5,1),('integer_string','1',1),('negative_generator',-1,0)]:
            run('R03',name[:-5]+'_word_'+label,name,lambda d,v=value,i=index,n=name:word(d,n)[0].__setitem__(i,v))
        if name==FILES[0]:run('R03','compact_word_missing',name,lambda d:d['terms'][0]['polynomial'][0].pop('word'))
        else:run('R03','Gram_Q_missing',name,lambda d:d.pop('Q'))
    for label,fun in [('false_theorem',lambda d:d.__setitem__('theorem','false different theorem')),('polynomial_order',lambda d:d.__setitem__('mu_polynomial',list(reversed(d['mu_polynomial'])))),('wrong_root',lambda d:d.__setitem__('root','smallest real root')),('field_descriptor',lambda d:d.__setitem__('scalar_encoding','different field'))]:run('R04',label,FILES[0],fun)
    run('R04','unknown_theorem_id',FILES[0],lambda d:d.__setitem__('theorem_id','different descriptive id'),['verify_sos14.py'],expect='annotative')
    run('R04','cached_status',FILES[2],lambda d:d.update(status='FALSE_CACHED_STATUS',coefficient_zero_residual=False),['verify_independent.py'],expect='annotative')
    run('R04','declared_support',FILES[1],lambda d:d['words'].append([[0,1]]),['verify_independent.py'],expect='annotative')
    run('R04','proof_text',FILES[0],lambda d:None,['verify_statement.py'],expect='annotative',extra=lambda r:(r/'PROOF.md').write_text('FALSE PROSE MUTATION: every strategy has Bell value 99.\n'))
    run('R04','joint_metadata',FILES[0],lambda d:d.update(theorem='false theorem',root='wrong root',scalar_encoding='wrong field'),extra=lambda r:(r/'PROOF.md').write_text('FALSE COORDINATED PROSE\n'))
    def explicit_zero(d):
        used={tuple(map(tuple,p['word'])) for p in d['terms'][0]['polynomial']}
        candidates=[[]]+[[[r,k]] for r in range(4) for k in range(1,5)]+[[[r,k],[s,l]] for r in (0,2) for s in (1,3) for k in range(1,5) for l in range(1,5)]
        w=next(w for w in candidates if tuple(map(tuple,w)) not in used);d['terms'][0]['polynomial'].append({'word':w,'coefficient':{'n':['0']*24,'d':'1'}})
    def unreduced(d):
        c=scalar(d);c['n']=[str(2*int(x)) for x in c['n']];c['d']=str(2*int(c['d']))
    def phase(d):
        for p in d['terms'][0]['polynomial']:
            c=p['coefficient'];n=list(map(int,c['n']));c['n']=list(map(str,[-x for x in n[12:]]+n[:12]))
    def scale(d):
        for p in d['terms'][0]['polynomial']:p['coefficient']['n']=[str(2*int(x)) for x in p['coefficient']['n']]
        d['terms'][0]['weight']['d']=str(4*int(d['terms'][0]['weight']['d']))
    def conjugation(d):
        for t in d['terms']:
            for p in t['polynomial']:
                c=p['coefficient'];c['n']=[str(-int(x) if i>=12 else int(x)) for i,x in enumerate(c['n'])]
                p['word']=[[r,5-k] for r,k in p['word']]
    for label,fun in [('explicit_zero',explicit_zero),('unreduced_rational',unreduced),('summand_permutation',lambda d:d['terms'].reverse()),('R_to_iR',phase),('R_to_2R_d_over4',scale),('compatible_conjugation',conjugation)]:run('R05',label,FILES[0],fun,['verify_sos14.py'],expect='pass')
    run('R05','duplicate_diagnostic_ID',FILES[0],lambda d:d['terms'][1].__setitem__('id',d['terms'][0]['id']),['verify_sos14.py'],expect='canonical')
    def coefficient(d):return d['terms'][0]['polynomial'][0]['coefficient']
    def modify_coefficient(d,f):
        c=coefficient(d);j=next(j for j,x in enumerate(c['n']) if int(x));c['n'][j]=str(f(int(c['n'][j])))
    def extra_support(d):
        explicit_zero(d);d['terms'][0]['polynomial'][-1]['coefficient']['n'][0]='1'
    def dropped(d):
        for p in d['terms'][0]['polynomial']:p['coefficient']['n']=['0']*24
    for label,fun in [('coefficient_plus1',lambda d:modify_coefficient(d,lambda x:x+1)),('true_coordinate_sign_reversal',lambda d:modify_coefficient(d,lambda x:-x)),('coordinate_tripling_distinct_control',lambda d:modify_coefficient(d,lambda x:3*x)),('dropped_summand',dropped),('extra_support_nonzero',extra_support),('zero_weight',lambda d:d['terms'][0]['weight'].__setitem__('n',['0']*24)),('negative_weight',lambda d:d['terms'][0]['weight'].__setitem__('n',[str(-int(x)) for x in d['terms'][0]['weight']['n']])),('nonreal_weight',lambda d:d['terms'][0]['weight']['n'].__setitem__(12,'1')),('invalid_state',lambda d:d.__setitem__('gamma',[copy.deepcopy(d['gamma'][0]) for _ in range(5)]))]:run('R11',label,FILES[0],fun,['verify_sos14.py'],expect='mathematical')
    # Guard checks target each real entrypoint, not just a shell wrapper.
    for ep in ['validate_integer_encoding.py','verify_sos14.py','verify_statement.py','verify_independent.py']:
        for label,flags,env in [('minus_O',['-O'],environment),('minus_OO',['-OO'],environment),('environment',[],{**environment,'PYTHONOPTIMIZE':'1'})]:
            cmd=[sys.executable,*flags,str(base/ep),'--root',str(base)];p=subprocess.run(cmd,text=True,capture_output=True,env=env);dest=a.output/'guards'/(ep+'_'+label);dest.mkdir(parents=True);(dest/'stdout.txt').write_text(p.stdout);(dest/'stderr.txt').write_text(p.stderr);row={'gate':'R13','label':label,'entrypoint':ep,'command':cmd,'returncode':p.returncode,'status':'PASS' if p.returncode!=0 and 'NORMAL_PYTHON_REQUIRED' in p.stderr else 'FAIL','stdout_sha256':sha(dest/'stdout.txt'),'stderr_sha256':sha(dest/'stderr.txt')};write(dest/'receipt.json',row);rows.append(row)
    write(a.output/'SUMMARY.json',{'status':'PASS' if all(r['status']=='PASS' for r in rows) else 'FAIL','enforced_target_sha256':baseline_target_hash,'source_sha256':sources,'rows':rows,'counts':{g:sum(r['gate']==g for r in rows) for g in ['R02','R03','R04','R05','R11','R13']}})
    raise SystemExit(0 if all(r['status']=='PASS' for r in rows) else 1)
if __name__=='__main__':main()

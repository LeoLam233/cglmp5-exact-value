#!/usr/bin/env python3
"""Portable fresh Phase-B scientific replay, retaining every failed attempt.

--root is the release repository; --phase-b is the extracted immutable checkpoint;
--output is a NEW directory. Original sources are staged byte-for-byte in the
layout they require. No copied historical receipt is accepted as a fresh result.
"""
import sys, os
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None,'','0'):
    raise SystemExit('REFUSED_OPTIMIZED_EXECUTION: exact scientific assertions require normal Python')
import argparse, concurrent.futures, datetime, hashlib, json, platform, shutil, subprocess, time
from pathlib import Path

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,x): p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def require(v,s):
    if not v: raise RuntimeError(s)
def manifest(root):return {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and '.git' not in p.parts}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--phase-b',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args()
    a.root=a.root.resolve();a.phase_b=a.phase_b.resolve();a.output=a.output.resolve();require(not a.output.exists(),'output must be new: stale receipts prohibited');a.output.mkdir(parents=True)
    stage=a.output/'stage';src=stage/'outputs/INDEPENDENT_CHECKS';receipts=stage/'outputs/RUN_RECEIPTS';payload=stage/'work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload'
    ignore=shutil.ignore_patterns('__pycache__','*.pyc')
    shutil.copytree(a.phase_b/'work',stage/'work',ignore=ignore);shutil.copytree(a.phase_b/'outputs/INDEPENDENT_CHECKS',src,ignore=ignore)
    for d in ['attainment','field','nc','bridge']: (receipts/d).mkdir(parents=True)
    # Frozen JSON tables must match revised release before their independent replay.
    science={}
    for n in ['SOS14.json','EXACT_KERNELS.json','EXACT_SOS_CANDIDATE.json','POSITIVITY_CERTIFICATE.json']:
        science[n]={'phase_b_sha256':sha(payload/n),'release_sha256':sha(a.root/'artifact_v0.1.1'/n)};require(len(set(science[n].values()))==1,'scientific table changed: '+n)
    write(a.output/'scientific_input_identity.json',science)
    write(a.output/'staging_manifest.json',{'source_root':str(a.phase_b),'stage_root':str(stage),'unchanged_source_copy':True,'work':manifest(stage/'work'),'scripts':manifest(src),'runner_sha256':sha(Path(__file__))})
    env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1','OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1'};env.pop('PYTHONOPTIMIZE',None)
    rows=[]
    def run(name,script,args=(),result=None,expect='PASS',check=None):
        cmd=[sys.executable,str(script),*map(str,args)];base=a.output/'runs'/name;base.mkdir(parents=True,exist_ok=False);t=time.monotonic()
        p=subprocess.run(cmd,cwd=base,env=env,text=True,capture_output=True)
        (base/'stdout.txt').write_text(p.stdout);(base/'stderr.txt').write_text(p.stderr)
        row={'name':name,'command':cmd,'cwd':str(base),'script_sha256':sha(script),'returncode':p.returncode,'elapsed_seconds':time.monotonic()-t,'python':sys.version,'platform':platform.platform(),'optimize':sys.flags.optimize,'stdout_sha256':sha(base/'stdout.txt'),'stderr_sha256':sha(base/'stderr.txt'),'semantic_status':'FAIL','unchanged_source_replay':True}
        try:
            require(p.returncode==0,'nonzero subprocess exit')
            data=json.loads(result.read_text() if result else p.stdout)
            require(data.get('status')==expect,'unexpected mathematical status: '+str(data.get('status')))
            if check: check(data)
            row['semantic_status']='PASS';row['semantic_result']=data
            if result:row.update(result_path=str(result),result_sha256=sha(result))
        except Exception as e:row['failure']=str(e)
        write(base/'receipt.json',row);rows.append(row);print(name,row['semantic_status'],row.get('failure',''),flush=True);return row
    def eq(x,k,v):require(x.get(k)==v,repr((k,x.get(k),v)))
    def field():
        run('R07_sturm_tarski',src/'field/sturm_tarski_weights.py',['--payload',payload,'--output',receipts/'field/sturm_tarski_weights.json'],receipts/'field/sturm_tarski_weights.json',check=lambda x:(eq(x,'real_root_count',6),eq(x,'largest_root_unique_above_3',True),require(len(x['weights'])==14,'14 weights')))
        run('R07_fraction_sign',src/'field/fraction_sign_meta.py',result=receipts/'field/fraction_sign_meta.json',check=lambda x:eq(x,'independent_exact_sign_comparisons',210))
        run('R08_embedding_crossmap',src/'field/review_attainment_field.py',result=receipts/'field/attainment_field_crossreview.json',check=lambda x:(eq(x,'basis_product_crosschecks',576),eq(x,'serialized_basis_crosschecks',24),eq(x,'cleared_norm_strictly_positive',True),eq(x,'attainer_denominator_d_gt_4',True)))
        run('R06_gram_linkage',src/'field/gram_elimination_recheck.py',result=receipts/'field/gram_elimination.json',check=lambda x:(eq(x,'exact_LDL_entry_checks',42),eq(x,'exact_E_L_compact_coefficient_checks',1134)))
    def exact():
        au=stage/'work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/INDEPENDENT_CHECKS'
        run('R06_A04_compact',au/'run_exact.py',['--payload',payload,'--receipt',receipts/'nc/A04_run_exact.json'],receipts/'nc/A04_run_exact.json',check=lambda x:(eq(x['SOS'],'expanded_union_support',273),eq(x['SOS'],'nonzero_residual_count',0),eq(x['conventions'],'deterministic_assignments',625)))
        run('R06_A04_full_gram',au/'run_gram.py',['--payload',payload,'--receipt',receipts/'nc/A04_run_gram.json'],receipts/'nc/A04_run_gram.json',check=lambda x:(eq(x,'word_union',1681),eq(x,'nonzero_residual_count',0),eq(x,'total_compact_term_matches',14)))
        run('R06_true_abelian_quotient',src/'nc/adjudicate_a06_commutativization.py',result=receipts/'nc/a06_commutativization.json',expect='CONFIRMED_AUDITOR_HARNESS_DEFECT',check=lambda x:(eq(x['results'],'baseline_noncommutative',True),eq(x['results'],'baseline_true_abelianization',True),eq(x['results'],'commutator_mutant_noncommutative',False),eq(x['results'],'commutator_mutant_true_abelianization',True)))
        run('R06_expanded_letter_normalizers',src/'nc/cross_audit_normal_forms.py',result=receipts/'nc/cross_audit_normal_forms.json')
        run('R06_finite_field_matrices',src/'nc/finite_field_matrix_attack.py',['--payload',payload,'--output',receipts/'nc/finite_field_matrix.json'],receipts/'nc/finite_field_matrix.json')
    def physical():
        run('R08_full_attainment',src/'attainment/exact_linkage.py',['--root',payload,'--output',receipts/'attainment/exact_linkage.json'],receipts/'attainment/exact_linkage.json',check=lambda x:(eq(x,'literal_event_coefficients',100),eq(x,'full_matrix_entry_comparisons',625),eq(x,'full_eigenvector_coordinates',25),eq(x,'saturation_total_coordinates',700),require(len(x['saturation_checks'])==28,'28 saturation vectors')))
        run('R10_generic_tensor_order',src/'attainment/a07_tensor_control.py',result=receipts/'attainment/a07_tensor_control.json',expect='CORRELATED_FIXTURE_BLIND_SPOT_CONFIRMED',check=lambda x:require(x['generic_wrong_tensor_order_Frobenius_error']>1 and x['generic_correct_order_Frobenius_error']<1e-12,'generic tensor controls'))
        run('R10_same_party_order',src/'nc/adjudicate_a06_matrix_order.py',result=receipts/'nc/a06_matrix_order.json',expect='CONFIRMED_AUDITOR_GENERAL_WORD_ORDER_DEFECT')
        run('R10_invalid_sample_diagnostics',src/'attainment/a07_sampling_health.py',result=receipts/'attainment/a07_sampling_health.json',expect='AUDITOR_HARNESS_DEFECT_CONFIRMED')
        a06=stage/'work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS'
        sf=next(a06.glob('*povm*'))
        run('R10_complete_five_outcome_samples',src/'attainment/probe_a06_search.py',['--source',sf,'--output',receipts/'attainment/a06_search_health.json'],receipts/'attainment/a06_search_health.json',expect='AUDITOR_HARNESS_DEFECT_CONFIRMED',check=lambda x:(eq(x,'trials',400),require(x['all_corrected_candidates_complete_error']<1e-10,'complete corrected PVMs')))
    def bridge():
        run('R09_exact_common_J',src/'bridge/exact_common_space.py',check=lambda x:(eq(x,'same_fixed_embedding',True),eq(x,'joint_operators_checked',200),eq(x,'assertion_count',1301)))
        run('R09_formal_proper_isometry',src/'bridge/formal_isometry_bridge.py',check=lambda x:(eq(x,'square_identity',True),eq(x,'naive_without_defect_rejected',True)))
        run('R09_compression_not_multiplicative',src/'bridge/compression_product_attack.py',expect='PASS_NEGATIVE_ROUTE_REJECTED')
        run('R09_wrong_setting_embedding',src/'bridge/a07_fixed_embedding_attack.py',expect='AUDITOR_OR_HARNESS_DEFECT_REPRODUCED',check=lambda x:require(x['one_fixed_embedded_entangled_state_max_probability_error']>1e-3,'fixed-state negative control'))
    def near():
        # Historical raw candidates and solver statuses are preserved as inputs only.
        historical=a.output/'historical_near_inputs';historical.mkdir()
        for name in ['a05_rational_candidate.json','a06_rational_candidate.json','a06_optimizer_replay.json','a06_optimizer_replay.npz']:
            shutil.copy2(a.phase_b/'outputs/RUN_RECEIPTS/attainment'/name,historical/name)
        a04=stage/'work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/rational_near_candidates.json'
        for label,data in [('a04',a04),('a05',historical/'a05_rational_candidate.json'),('a06',historical/'a06_rational_candidate.json')]:
            run('R12_'+label+'_exact_envelopes',src/'attainment/integer_envelopes.py',['--data',data,'--output',receipts/f'attainment/{label}_integer_envelope.json'],receipts/f'attainment/{label}_integer_envelope.json')
        write(historical/'INPUT_SHA256SUMS.json',manifest(historical))
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
        futures=[ex.submit(f) for f in [field,exact,physical,bridge,near]]
        for f in futures:
            try:f.result()
            except Exception as e: rows.append({'name':'runner_failure','semantic_status':'FAIL','failure':repr(e)});print('RUNNER_FAILURE',repr(e),flush=True)
    write(a.output/'SUMMARY.json',{'status':'PASS' if all(r['semantic_status']=='PASS' for r in rows) else 'FAIL','scope':'Fresh scientific component replay; gate integration still requires R01–R05,R11,R13,R14 and analytic/editorial review. Matrix/numerical results are diagnostics, not independent universal proofs.','runs':[{k:v for k,v in r.items() if k!='semantic_result'} for r in rows],'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
    raise SystemExit(0 if all(r['semantic_status']=='PASS' for r in rows) else 1)
if __name__=='__main__':main()

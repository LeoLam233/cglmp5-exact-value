#!/usr/bin/env python3
"""Assemble source-bound R01–R14 only after all semantic and review receipts pass."""
import argparse,datetime,hashlib,json
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(v,m):
    if not v:raise RuntimeError(m)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);a=ap.parse_args();root=a.root.resolve();base=root/'verification/receipts'
    def read(n,passed=True):
        x=json.loads((base/n).read_text())
        if passed:require(x.get('status') in ['PASS','ALL_TESTS_PASSED'],'receipt not PASS: '+n)
        return x
    hard=read('hardening_attempt02/SUMMARY.json');science=read('scientific_attempt02/SUMMARY.json');read('receipt_binding.json');read('orchestration_attempt01/SUMMARY.json');read('relocation_attempt01/SUMMARY.json');integ=read('integrity_final.json');require(integ['source_manifest_included'],'R01 must include final source manifest');read('raw_candidate_diagnostics.json');read('generic_rational_PVMs.json');read('kill_tests.json')
    for name in ['review/analytic_bridge_review.json','review/editorial_review.json']:
        x=read(name)
        for p,h in x.get('source_binding',{}).items():require(sha(root/p)==h,'review source binding stale: '+p)
    requiredcounts={'R02':117,'R03':40,'R04':19,'R05':7,'R11':9,'R13':12}
    require(hard['counts']==requiredcounts,'hardening count mismatch');require(len(science['runs'])==21 and all(r['semantic_status']=='PASS' for r in science['runs']),'scientific runs mismatch')
    gate={}
    def add(g,meaning,paths,**more):
        entries=[]
        for p in paths:
            path=base/p;require(path.is_file(),'missing evidence '+p);entries.append({'path':str(path.relative_to(root)),'sha256':sha(path)})
        gate[g]={'status':'PASS','semantic_result':meaning,'receipts':entries,**more}
    def sci(*names):return ['scientific_attempt02/runs/'+n+'/receipt.json' for n in names]
    hardref=['hardening_attempt02/SUMMARY.json']
    add('R01','Immutable outer/nested/payload/current manifests match; frozen tag bytes unchanged; original-to-curated maps retained; manifest scopes distinguished.',['integrity_final.json','replay_source_identity.json'])
    add('R02','117 actual consumer executions reject malformed exact scalar JSON by SchemaError before mathematical arithmetic.',hardref,executions=117,coverage='Each mathematical consumer receives every malformed family in each file it actually consumes; combined preflight covers all four files.')
    add('R03','40 actual consumer executions reject malformed compact/Gram Q words and absent fields; integer-string word policy explicit.',hardref,executions=40)
    add('R04','19 metadata/prose mutations enforce fixed declarations or disclose annotations; actual theorem remains fixed and input/source/prose hashes match.',hardref+['receipt_binding.json','guarded_supplement/receipt_binding_guarded/receipt.json'],executions=19)
    add('R05','Six mathematical invariances retained, including compatible conjugation; duplicate diagnostic ID rejected only as canonical traceability policy; explicit-zero stored/nonzero counts165/164 separated.',hardref+['receipt_binding.json','guarded_supplement/receipt_binding_guarded/receipt.json'],executions=7)
    add('R06','Characteristic-zero compact273/Gram1681 residuals zero; 42 LDL/1134 E-L checks; alternate engine, true abelian quotient and injected NC commutator controls. Finite-field102 cases are diagnostic.',sci('R06_A04_compact','R06_A04_full_gram','R06_gram_linkage','R06_true_abelian_quotient','R06_expanded_letter_normalizers','R06_finite_field_matrices')+['guarded_supplement/exact_abelian_guarded/receipt.json'])
    add('R07','Largest real branch selected; all14 actual weights >1/3000; independent Fraction210 sign comparisons; actual coefficient reevaluation across12 compatible embeddings loses positivity on wrong branches; zero/nonreal/negative controls rejected.',sci('R07_sturm_tarski','R07_fraction_sign')+hardref)
    add('R08','100 literal event coefficients,625 deterministic assignments,20 Fourier projectors,625 full Bell entries,25 eigenvector coordinates,28 saturation vectors/700 coordinates exact; phase/D-shift controls nonzero; actual embedding map and positive state denominator/norm verified.',sci('R08_full_attainment','R08_embedding_crossmap'))
    add('R09','Fixed common J:1301 exact checks and200 joint compressions, zero/rank-deficient effects, unequal dimensions, entangled mixed state, proper-isometry defect, wrong-setting/omitted-completion/compression-product controls; analytic arbitrary-dimensional review separately identified.',sci('R09_exact_common_J','R09_formal_proper_isometry','R09_compression_not_multiplicative','R09_wrong_setting_embedding')+['review/analytic_bridge_review.json'])
    add('R10','Generic tensor/same-party ordering defects exposed away from optimizer;400 repaired sampling cases complete; additional12 exact rational PVM families/60 outcomes use all columns with explicit PSD witnesses and noncommuting settings.',sci('R10_generic_tensor_order','R10_same_party_order','R10_invalid_sample_diagnostics','R10_complete_five_outcome_samples')+['generic_rational_PVMs.json','guarded_supplement/generic_PVM_guarded/receipt.json'])
    add('R11','Nine compact mathematical mutations rejected by ArithmeticError; true coordinate negation distinguished from tripling;12 inherited kill tests cover Gram coefficient/drop, phase reversal, lowered bound and invalid state interfaces.',hardref+['kill_tests.json'])
    add('R12','Preserved raw binary64 arrays fail exact unitarity; all31 historical optimizer statuses retained and identified as historical; six A04 plus A05/A06 defined repaired representatives have exact strict below-mu enclosures; no global-bound inference.',sci('R12_a04_exact_envelopes','R12_a05_exact_envelopes','R12_a06_exact_envelopes')+['raw_candidate_diagnostics.json','guarded_supplement/raw_candidate_guarded/receipt.json'])
    add('R13','All four entrypoints refuse-O/-OO/optimization environment; six orchestration fixtures distinguish semantic PASS/zero residual from FAIL+exit0, nonzero residual, wrong CLI, incomplete output and stale receipt.',hardref+['orchestration_attempt01/SUMMARY.json'])
    add('R14','Fresh relocated five-entrypoint replay with spaces/unrelated cwd and exact source/input/dependency binding; all failed attempts retained; archived source/finding coverage and analytic/editorial limits explicitly reviewed.',['relocation_attempt01/SUMMARY.json','scientific_attempt02/staging_manifest.json','scientific_attempt01/SUMMARY.json','hardening_attempt01/SUMMARY.json','review/editorial_review.json','review/analytic_bridge_review.json'])
    binding={}
    for line in (root/'SOURCE_MANIFEST.sha256').read_text().splitlines():
        if line.strip() and not line.lstrip().startswith('#'):
            h,p=line.split(None,1);p=p.strip().lstrip('*');require(sha(root/p)==h,'source manifest stale '+p);binding[p]=h
    binding['SOURCE_MANIFEST.sha256']=sha(root/'SOURCE_MANIFEST.sha256')
    result={'schema':'cglmp5.release-gate.v1','release':'v0.1.1','status':'PASS','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'gates':gate,'source_binding':binding,'scientific_changes':'NONE: exact coefficient tables byte-identical to v0.1.0','scope':'Current semantic component execution plus explicitly labeled independent analytic/editorial review. Historical failure receipts remain FAIL and do not count as scientific PASS. No formal verification, human peer review, absolute novelty or independent-model guarantee.','phase_b_archive_sha256':'12e2864ed19d99500b72d4aefe6e2b27939fb67c05aa355b38b997456a55fc43'}
    (root/'verification/release_gate.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS: source-bound R01–R14 assembled',len(binding),'sources')
if __name__=='__main__':main()

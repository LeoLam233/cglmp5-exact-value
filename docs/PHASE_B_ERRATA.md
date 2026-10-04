# Phase-B appended evidence errata and claim crosswalk

This is an **additive v0.1.1 interpretation of frozen evidence**, not a replacement of any original report, script, receipt, ZIP or checksum. Its controlling source is the final Phase-B master ledger and associated coverage matrix. Historical mistakes and partial runs remain in the immutable archive.

Phase-B verdict: `SURVIVED_MULTI_AUDIT_CORRELATED_FAILURE_ATTACK`.
Revision class: `NONLOAD_BEARING_HARDENING_ONLY`.
No confirmed load-bearing mathematical defect was adjudicated. This does not mean that all archived tests succeeded, that every script was fully replayed, or that an unknown flaw is impossible.

## How to resolve the evidence

All source paths in the evidence index below are **relative to the root of the final Phase-B ZIP**, not this repository or the containing directory of a script:

- Archive: `CGLMP5_PhaseB_checkpoint_20261004T092328Z_FINAL_COMPLETE.zip` (a supplied download may append `(1)` to its filename).
- Archive SHA-256: `12e2864ed19d99500b72d4aefe6e2b27939fb67c05aa355b38b997456a55fc43`.
- Ledger: `outputs/MASTER_FINDINGS_LEDGER.json` and `.md` (byte-preserved [repository copy](../audits/phase_b_2026-10-04/MASTER_FINDINGS_LEDGER.json)).
- Coverage: `outputs/AUDITOR_COVERAGE_MATRIX.json` and `.md`.
- Scope/dependence: `outputs/FINAL_PHASE_B_REPORT.md` and `outputs/CORRELATED_FAILURE_REPORT.md`.
- Prospective accepted work: `outputs/CONSOLIDATED_REVISION_PLAN.md` and `outputs/REGRESSION_TEST_PLAN.md`.

The normalized paths preserve the original A01–A07 trees under `work/expanded/`. A few ledger paths are output-root-relative (`RUN_RECEIPTS/...`, `lanes/...`); this index explicitly prefixes them with `outputs/` rather than silently treating the archive root as their base. No source file was changed to normalize a path. Each indexed source hash was rechecked against both the supplied extracted copy and the immutable final ZIP while preparing this errata. That check authenticates referenced bytes; it is not a new execution of the archived scientific test.

## Corrections that affect interpretation most

- A01: its numerical corroboration can print PASS under optimized Python after assertions disappear; its exact core has distinct behavior. A relabel control rejected duplicate support, not the intended residual. Source was viewed before its formal precheck plan, limiting procedural-blindness language (B-S29, B-S34, NC-014).
- A02: accepting an explicit zero coefficient is a mathematical no-op; the stored record count must not be described as the count of nonzero coefficients (B-S07). Its other source-level checks retain their recorded scope.
- A03: initial fixture selectors stopped before the requested mutations. Later corrected runs do not erase those failures. Preserve optimizer precision-loss statuses and distinguish a high-precision diagnostic from a rigorous global bound (B-S26, B-AT08).
- A04: an incorrect CLI invocation and timed-out/resumed sweeps are not mathematical rejection receipts. The 164-coefficient sweep is exact perturbation-delta testing with 14 full-term crosschecks, not 164 complete verifier executions. Rational envelopes concern explicitly repaired nearby physical strategies (B-S27, NC-016, B-AT09).
- A05: preserve corrected parser/arithmetic development failures. A valid wider enclosure is not a corruption. Its repaired near-optimal physical representative is distinct from the raw nonunitary arrays (B-S28, FIELD-011/012, B-AT10).
- A06: the encoding audit was not strict; the purported abelianization was not the abelian quotient; a generic same-party evaluator reversed factor order. Discount 105 of 400 incomplete supplementary PVM fixtures. Its 49-digit check actually used a binary64 prefix; its optimizer omitted status/arrays, and a Phase-B replay recorded 0 successful terminations out of 31 starts (B-S18, NC-004/005, B-AT06/11/14).
- A07: coordinate tripling is not a sign flip; changing only the target bound is not an alternate-embedding test; exact FAIL can exit zero. Its common-space test changed the embedded state with the settings. A generic odd-edge tensor-order bug is exactly masked by the special Fourier fixture. Discard incomplete d=6/7 PVM samples and invalid rank-one POVM fixtures. Its floating positivity and aborted modular-size route supply no rigorous positivity/upper-bound evidence; the final exact integer path remains distinct (B-S17–B-S25, B-E01/02, FIELD-007/008, NC-012/024, B-AT04–07/17).

The findings below retain successful evidence where valid. A defect in an auditor's implementation is not automatically a defect in the frozen theorem; conversely, an audit's summary PASS does not rescue its defective component.

## Scientific scope retained

The characteristic-zero SOS identity, actual real embedding and strict positive weights carry the upper bound. The analytic bounded-operator argument and a **single fixed embedding for both local measurement settings** extend it to arbitrary-dimensional local tensor-product five-outcome POVMs. The explicit physical strategy attains the same bound in the full 25-dimensional space. Finite matrix, finite-field, optimization and SDP checks remain diagnostic or cross-representation controls with their stated limitations. The commuting-PVM upper bound does not silently add an abstract commuting-POVM theorem.

The formal coefficient presentation need not be irreducible for an exact-zero implication. Actual root selection, denominator nonvanishing, reality and strict positivity are separate obligations. Gram and compact certificates share the same fourteen weights; checking both is extra serialized-data-path coverage, not fourteen new positivity facts. No claim of self-testing, uniqueness, arbitrary outcome number, absolute priority, human peer review or proof-assistant verification is added.

## Complete finding crosswalk

The 110 controlling rows include 21 explicit aliases. The 89 non-alias rows comprise 6 confirmed non-load-bearing verifier/documentation defects, 37 auditor/harness defects, 39 benign acceptances or scope limits and 7 misreports/rejected findings. These are dispositions, not independent votes. Text below records the Phase-B adjudication; it does not assert that the corresponding v0.1.1 regression has already passed. Current regression status belongs to the separately source-bound release receipts. Repository copies of the controlling outputs and their original paths/hashes are in [the preserved source map](../audits/phase_b_2026-10-04/PRESERVED_SOURCE_MAP.json).

### B-S01: Scalar float/Boolean coercion in standalone mathematical entrypoints

Disposition: `CONFIRMED_NONLOAD_BEARING_DEFECT`.

load_scalar/read_interval use int() and therefore can truncate nonintegral JSON numbers or accept booleans. Strict separate preflight rejects demonstrated scalar cases; exact frozen input is well formed. No altered decoded false identity was accepted.

Required interpretation/action: Require one shared strict decoder at every entrypoint; preserve frozen v0.1 bytes.

Original claim labels: `H02 ALG-01`; `A01 G-03/N1`; `A02 G-003`; `A03 N1`; `A04 NL-01`; `A05 NL1`.

Original / source evidence: [E132](#e132) (archived lines 118,119,147,148), [E054](#e054)

Recorded Phase-B reproductions: [E045](#e045)

### B-S02: Duplicate JSON keys use last-value semantics in mathematical entrypoints

Disposition: `CONFIRMED_NONLOAD_BEARING_DEFECT`.

Plain json.loads accepts duplicate scalar or top-level keys. Separate preflight unique_object rejects duplicates. This is malformed-input acceptance, not a false identity on frozen bytes.

Required interpretation/action: Use duplicate-key rejection for all mathematical JSON reads.

Original claim labels: `A01 G-04/N2`; `A02 G-002`; `A03 N2`; `A04 NL-01`; `A05 C07`.

Original / source evidence: [E133](#e133) (archived lines 10), [E131](#e131) (archived lines 16,19,24)

Recorded Phase-B reproductions: [E045](#e045)

### B-S03: Compact word float/Boolean aliases accepted by equality semantics

Disposition: `CONFIRMED_NONLOAD_BEARING_DEFECT`.

Integral float exponents and Boolean generator labels can equal the intended integers and pass core; named word preflight rejects them. No changed represented word escapes the mathematical test.

Required interpretation/action: Require actual integer word factors in all consumer paths.

Original claim labels: `A04 floating_integral_word_exponent`; `A05 C04/C05`.

Original / source evidence: [E132](#e132) (archived lines 130,134,135,194,196,199,248,282), [E080](#e080) (archived lines 75,105,139,1055)

### B-S04: Strict preflight misses Gram Q syntax

Disposition: `CONFIRMED_NONLOAD_BEARING_DEFECT`.

Q is stored as nested arrays rather than objects named word. Preflight therefore accepts Boolean/integral-float aliases even in a combined pipeline. Phase B combined Q=[true,1.0] passes both checks; [true,1.1] fails Gram, showing equality-preserving type aliases only.

Required interpretation/action: Add explicit required Q schema validation before mathematical comparison.

Original claim labels: `A05 NL2/G10/G11`.

Original / source evidence: [E131](#e131) (archived lines 39,50), [E132](#e132) (archived lines 211,212)

Recorded Phase-B reproductions: [E045](#e045)

### B-S05: Missing scalar members pass syntax-only preflight but fail mathematical consumer

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Traversal recognizes scalar objects only if both n and d exist. Removing one means the preflight skips that malformed object; mathematical checker raises KeyError. Preflight explicitly claims syntax-only scope, so combined check fails closed.

Required interpretation/action: Document limited scope or upgrade to full required schema; do not portray preflight alone as certification.

Original claim labels: `A04 NL-02/missing_scalar_n/missing_scalar_d`.

Original / source evidence: [E131](#e131) (archived lines 4,29,59), [E065](#e065) (archived lines 152,958)

Recorded Phase-B reproductions: [E045](#e045)

### B-S06: Integer-string word schema mismatch is fail-closed

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Preflight permits integer strings in a word, while canon expects integer generator operations and rejects strings. This rejects an arguably permissible encoded input rather than accepting a false result.

Required interpretation/action: Choose and enforce one documented word-type schema.

Original claim labels: `A04 integer_string_generator_interface`; `A05 C26`.

Original / source evidence: [E080](#e080) (archived lines 75,538,547)

### B-S07: Added explicit zero is mathematical no-op, storage count is not nonzero count

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Appending a zero record at unused support keeps the SOS identical; core reports explicit_polynomial_coefficients=165. Frozen table actually has 164 nonzero coefficients. A02 calls this a defect, but acceptance is benign absent a canonical nonzero-support promise on arbitrary inputs; the output field itself does not say nonzero.

Required interpretation/action: Either prohibit explicit zeros as canonical schema or label counts stored/nonzero separately. Do not require a scientific repair.

Original claim labels: `A02 G-004/NLB-02`; `A03 G16/semantic boundary`; `A05 C30`.

Original / source evidence: [E133](#e133) (archived lines 26,31), [E056](#e056) (archived lines 11,88,130,150,152,162,252,253,259,270,272,275,278,324)

Recorded Phase-B reproductions: [E045](#e045)

### B-S08: Theorem descriptors and proof bytes are not bound to checker PASS

Disposition: `CONFIRMED_NONLOAD_BEARING_DEFECT`.

All mathematical entrypoints check hard-coded mathematics, not PROOF.md or every descriptor. Coordinated Phase-B false-theorem/proof/polynomial/field mutations all pass preflight and mathematical entrypoints. This exposes interface-level statement binding, while the actual frozen statement is separately reconciled by scientific lanes. No proof of maximum 2 was obtained.

Required interpretation/action: Emit checker version, authoritative theorem identifier and verified input digests; explicitly separate annotations from enforced claims; bind frozen proof/document hashes in release wrapper.

Original claim labels: `A03 wrong_descriptive_mu_polynomial`; `A04 NL-03`; `A05 NL3/C23/C24/C25/G09`.

Original / source evidence: [E134](#e134) (archived lines 2,17,20,26,28,29,30,31,33,40), [E130](#e130) (archived lines 2,3,13,14)

Recorded Phase-B reproductions: [E045](#e045)

### B-S09: Ignoring cached PASS flags, stored word universes and pivot enclosures is intentional

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Reconstructing words, positivity and residuals rather than trusting diagnostic annotations is desirable. Flipping/erasing annotations must not be mistaken for a harmful mathematical mutation.

Required interpretation/action: Keep recomputation; explicitly mark ancillary/historical fields non-authoritative.

Original claim labels: `H03 stored PASS flags ignored`; `A04 legacy_*`; `A05 G01/G08`; `A07 NL-4`.

Original / source evidence: [E132](#e132) (archived lines 8,9,213), [E080](#e080) (archived lines 551,695)

### B-S10: Duplicate diagnostic term IDs are benign to algebra but weak for provenance

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

The sum is indexed by list entries, not ID lookup. Duplicate IDs change diagnostics only and still pass mathematical checks. A stricter canonical certificate may prohibit them without changing theorem.

Required interpretation/action: Enforce unique IDs for traceability if adopting strict schema.

Original claim labels: `A04 duplicate_term_ID_ignored`; `A05 C09`.

Original / source evidence: [E133](#e133) (archived lines 12,13), [E081](#e081) (archived lines 218)

Recorded Phase-B reproductions: [E045](#e045)

### B-S11: Valid rescaling, common phase, summand order and unreduced rationals remain valid

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Consistent conjugation of both sides, R→2R with d→d/4, R→iR, summand permutation and unreduced rational encodings preserve represented mathematics. Acceptance is a positive control, not weakness.

Required interpretation/action: Retain benign-control regressions alongside corruption tests.

Original claim labels: `A03 G31`; `A05 C27/C28/C31/C34`.

Original / source evidence: [E078](#e078), [E060](#e060) (archived lines 332)

### B-S12: Rejection of equivalent noncanonical words is a format scope limit

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Splitting coefficients into duplicate records, cross-party raw word reversal and exponents 6 modulo 5 are algebraically equivalent but outside declared canonical input form. Rejection is not a theorem defect.

Required interpretation/action: Document canonical encoding and distinguish semantic corruption from canonical-format rejection.

Original claim labels: `A05 C29/C32/C33/G13`.

Original / source evidence: [E078](#e078)

### B-S13: Dangling historical references in scientific payload

Disposition: `CONFIRMED_NONLOAD_BEARING_DEFECT`.

PROOF refers to NOVELTY_AND_SCOPE_AUDIT.md and EXACT_KERNELS declares field_relations_file exact_field.py, neither in reduced Phase-A payload. These are historical/provenance pointers; theorem is self-contained from displayed relations and serialized data.

Required interpretation/action: Mark references as historical/excluded and identify original-release paths; do not import missing code as proof premise.

Original claim labels: `A06 NLB-1/NLB-2`.

Original / source evidence: [E128](#e128) (archived lines 260), [E125](#e125) (archived lines 65113), [E082](#e082) (archived lines 125,126)

### B-S14: Historical positivity-not-yet-certified status is not current evidence

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

EXACT_SOS_CANDIDATE status records an earlier identity-only stage. Separate positivity certificate and actual recomputation establish positivity. Reading status in isolation is misleading but not inconsistent mathematics.

Required interpretation/action: Label status historical or remove stale annotation in a separately versioned package.

Original claim labels: `A06 NLB-3`.

Original / source evidence: [E126](#e126) (archived lines 2), [E082](#e082) (archived lines 127)

### B-S15: Nonconsecutive block labels do not contradict five blocks

Disposition: `MISREPORT_OR_REJECTED_FINDING`.

Labels [1,6,7,8,9] identify five blocks; no promise of consecutive numbering is violated. The observation is not a defect.

Required interpretation/action: Reject proposed scientific repair; optional explanatory label note only.

Original claim labels: `A06 NLB-4`.

Original / source evidence: [E126](#e126) (archived lines 13), [E082](#e082) (archived lines 128)

### B-S16: Correct k=0,1 convention is not a non-load-bearing defect

Disposition: `MISREPORT_OR_REJECTED_FINDING`.

Frozen standard five-outcome formula uses k=0,1. Comparing to a deliberately doubled 0..4 expression is a normalization control, not an error in frozen formula.

Required interpretation/action: Retain standard convention; route numerical coefficient comparison to convention lane.

Original claim labels: `A06 NLB-5`.

Original / source evidence: [E082](#e082) (archived lines 129)

### B-S17: A07 no-silent-coercion claim is contradicted by inspected source

Disposition: `MISREPORT_OR_REJECTED_FINDING`.

Claim that no silent coercion path was found cannot be used as evidence of strict parser coverage: author load_scalar plainly int-coerces, and A07 own parser also int-coerces. Phase-B replays reproduce accepted malformed encodings. A06 no-checker-defect report likewise must be narrowed to its actual checks.

Required interpretation/action: Correct coverage to frozen-data parse only; count strong malformed-input tests from A01–A05 rather than vote counts.

Original claim labels: `A07 G-01`.

Original / source evidence: [E097](#e097) (archived lines 40,60,79), [E106](#e106) (archived lines 189,198)

Recorded Phase-B reproductions: [E045](#e045)

### B-S18: A06 independent encoding audit is not strict

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Extracted original encoding walk accepts denominator 1.5, Boolean generator, exponent1.9 and malformed integer string --3 with zero bad-scalar/word count. These are actual component executions. Frozen data remain clean; the alleged parser negative-control coverage was overstated.

Required interpretation/action: Replace int()/lstrip-is-digit validation with exact types/canonical strings, complete Q and fraction schemas, and executable malformed-input controls.

Original claim labels: `A06 G-002/R14`.

Original / source evidence: [E091](#e091) (archived lines 44,47,53,128), [E083](#e083) (archived lines 299,301)

Recorded Phase-B reproductions: [E042](#e042)

### B-S19: A07 sign-flip controls actually triple a coordinate

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

bump(o,idx,2*n) yields n+2n=3n, not -n. Both selected coordinates are positive before and after. These tests detect coefficient changes but provide no sign-flip-specific evidence.

Required interpretation/action: Correct mutators to negate; Phase B freshly ran both true sign controls and both were rejected. Prior report must call historical tests coordinate tripling.

Original claim labels: `A07 G-02/M3/M6`.

Original / source evidence: [E110](#e110) (archived lines 116,121,124)

Recorded Phase-B reproductions: [E042](#e042), [E043](#e043)

### B-S20: A07 alternate-root control only changes target constant

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

identity_residual(mu=alt) changes lhs constant but parse uses global MONO formed from MU_TRUE. Coefficients remain in original embedding. This is a valid wrong-bound test, not certificate reevaluation at another root.

Required interpretation/action: Relabel evidence and use actual full-field alternate embeddings from root lane for branch coverage.

Original claim labels: `A07 M13/M-D`.

Original / source evidence: [E110](#e110) (archived lines 21,22,24,29,48,49,122,123,139), [E123](#e123) (archived lines 15,50)

Recorded Phase-B reproductions: [E042](#e042)

### B-S21: A07 exact checker exits zero even for explicit FAIL

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Archived M2 gives 201 nonzero residuals and EXIT=0. Fresh Phase-B original-source M1 gives 37 nonzero residuals, verdict FAIL and exit0. An exit-code-only harness would misclassify both. Baseline exact zero residual is not invalidated.

Required interpretation/action: Return nonzero for failed mathematical status and require receipt status/residual, not exit alone.

Original claim labels: `A07 G_exact_on_M2`; `PhaseB tiny coefficient mutation`.

Original / source evidence: [E106](#e106) (archived lines 294,295,297,299), [E121](#e121) (archived lines 25,45,48)

Recorded Phase-B reproductions: [E042](#e042)

### B-S22: A07 aggregate mutation summary does not reproduce final all-16 claim

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Delivered g_mutation_controls executes13 named cases and retains three false values. M1/M2 numerical misses are expected precision limits; M2 exact replay is archived, M1 standalone exact receipt/mutant is absent but reproduced freshly in Phase B. Appended M11b results are not generated by delivered g source; benign widened box is correctly admissible. Final all16 summary cannot be obtained from one delivered driver.

Required interpretation/action: Preserve old misses, add consolidated reproducible exact/box runner and checked final summary with input/source hashes.

Original claim labels: `A07 G-02`; `G_summary.json`; `G_receipt.txt`.

Original / source evidence: [E100](#e100), [E122](#e122), [E110](#e110) (archived lines 104,115,119,136,141,143,144,145,150)

Recorded Phase-B reproductions: [E042](#e042)

### B-S23: A07 polynomial order and annotation-location prose are wrong

Disposition: `MISREPORT_OR_REJECTED_FINDING`.

SOS14.mu_polynomial [5,0,-65,0,144,96,16] is descending for stated sextic, not ascending. coefficient_zero_residual is a candidate annotation, not a positivity-certificate field. These are auditor report errors; core exact target is not changed.

Required interpretation/action: Correct report metadata descriptions; require field-name/location/order checks.

Original claim labels: `A07 NL-4`.

Original / source evidence: [E098](#e098) (archived lines 205,207), [E130](#e130) (archived lines 3), [E126](#e126) (archived lines 2754)

### B-S24: A07 Gram redundancy argument overstates byte coverage

Disposition: `MISREPORT_OR_REJECTED_FINDING`.

Compact SOS is sufficient for universal theorem independently of redundant Gram data. Matching81 basis words does not validate every E,H,L,D coefficient or prove compact–Gram equivalence. Other audits independently check that bridge.

Required interpretation/action: Mark A07 Gram/LDL as author replay/partial structural check, not independent exact Gram reconstruction; do not count redundant claims as extra independent votes.

Original claim labels: `A07 NL-3/N1/M-E`.

Original / source evidence: [E098](#e098) (archived lines 197,200,201), [E112](#e112) (archived lines 23,28,42,44,119,121)

### B-S25: A07 failed partial diagnostics must not be counted as complete successful runs

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Earlier C receipt says FAIL; C_probe completes variant diagnostics but crashes on tuple-unpacking display; C_size stops at Python integer-to-string digit limit. Corrected exact C source/receipt supplies identity evidence; successful pre-error diagnostic values retain only their actually completed scope. Earlier B/F correction paths are distinct from final outputs.

Required interpretation/action: Retain partial records with terminal status, narrow coverage to completed steps, and provide final corrected driver receipts.

Original claim labels: `C_receipt`; `C_probe_receipt`; `C_size_receipt`; `B_receipt`; `F_receipt`.

Original / source evidence: [E118](#e118) (archived lines 26,27,28,29,30,31,32,33,34,35,36,37,38,39), [E117](#e117) (archived lines 4,5,6,7,34,38), [E119](#e119) (archived lines 9,13)

### B-S26: A03 and A04 initial mutation selectors aborted before intended checks

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

The selected dense coefficient had no zero slot. StopIteration is fixture construction failure, not rejection of a malformed certificate. Later corrected complete receipts supersede the failed runs; both failures preserved.

Required interpretation/action: Keep failures excluded from successful coverage and regression-test fixture selection.

Original claim labels: `A03 attempt1 StopIteration`; `A04 independent_controls.initial_failed`.

Original / source evidence: [E058](#e058), [E057](#e057), [E059](#e059), [E061](#e061), [E066](#e066)

### B-S27: A04 argument-error rejection and partial sweeps are distinct from mathematical tests

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Initial new-support author invocation exited2 due to positional path instead of --root, not SOS residual. Corrected replay rejects with explicit residual.164-coefficient sweep uses sparse perturbation differences with14 full-term checks, not164 full executions. Chunked/resumed complete receipts replace timeouts.

Required interpretation/action: Preserve exact error categories and coverage granularity; validate stderr/status alongside return code.

Original claim labels: `A04 meta_exact.invalid_author_invocation`; `A04 controls partial/author chunked runs`.

Original / source evidence: [E064](#e064), [E068](#e068) (archived lines 6,7), [E069](#e069) (archived lines 7)

### B-S28: A05 development parser and arithmetic failures were corrected, not theorem failures

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Original primitive parser wrongly rejected ancillary decimal metadata; positivity class initially lacked reverse subtraction; a supposedly invalid u enclosure was actually valid; a dead conjugation assertion and tautological N/N check required real cross-checks. Final sources/receipts document corrections and replay.

Required interpretation/action: Retain exact failure scope, corrected-source hashes and independent norm/Fourier tests; do not count aborted attempts as successful evidence.

Original claim labels: `A05 independent_primitives.attempt1`; `positivity development_run_1/2`; `dead Fourier assertion`; `N/N normalization`.

Original / source evidence: [E079](#e079), [E075](#e075), [E076](#e076), [E071](#e071) (archived lines 82,124)

### B-S29: A01 numerical checker can falsely emit PASS with assertions disabled

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

On weight+1 corruption, original A01 concrete checker rejects normally but -O removes final asserts and emits PASS despite residuals>1. Frozen author checker still rejects under -O. The A01 exact core uses explicit need checks, so this finding is limited to numerical corroboration/runtime flag semantics.

Required interpretation/action: Add optimize guard or explicit failure checks, record optimize flag, and require results to satisfy declared numerical thresholds.

Original claim labels: `PhaseB -O attack`.

Original / source evidence: [E053](#e053) (archived lines 64,65)

Recorded Phase-B reproductions: [E044](#e044)

### B-S30: Author entrypoints and several audit paths are correlated evidence families

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

verify_sos14 and verify_statement import verify_independent arithmetic/normalizer/interval logic; H03 is author-side mutation of same engine. Each auditor mostly shares one scalar/parser/reducer within its exact suite. Different models/prompts do not imply independent target semantics. H01 second tower checker and alternate modular/direct-matrix paths add genuinely distinct implementation dimensions with explicit limits.

Required interpretation/action: Use per-node ancestry matrix, not majority PASS. Compact/Gram identical weights are one positivity object, not two independent proofs.

Original claim labels: `A07 M-A/NL-1`; `A06 M1/M3`; `all independence caveats`.

Original / source evidence: [E133](#e133) (archived lines 7), [E134](#e134) (archived lines 8), [E083](#e083) (archived lines 112,200,283,286,287,345,393), [E137](#e137) (archived lines 4,7)

### B-S31: Hashes establish supplied byte identity, not external provenance or audit blindness

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

All outer corpus hashes and current manifests identify supplied bytes. They do not independently authenticate commit history, publication time, authorship, actual model isolation or unavailable historical input. H02 explicitly discloses prior AI notes and incomplete generation history; no external project lookup was performed in Phase B.

Required interpretation/action: Keep provenance claims bounded; no theorem premise may rely on unseen history or novelty status.

Original claim labels: `source release identity`; `historical exposure`; `novelty limits`.

Original / source evidence: [E124](#e124), [E048](#e048) (archived lines 3,7,11,17,24,30,32,37,40,44,48,50,61,62,68,76,78,86,105,107)

### B-S32: Historical nested manifest mismatch is disclosed path normalization

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Two nested historical checksums differ from curated report/environment text; packaging_identity maps source hashes to current hashes and current outer MANIFEST validates all bytes. A05 branch manifests likewise use archive-root relative paths and all123 entries verify from declared root; initial wrong-base checks are not corruption.

Required interpretation/action: Label historical manifests and required cwd; retain original→curated mapping. Do not rewrite historical hashes as if original receipts were unchanged.

Original claim labels: `BASE-RELEASE lower_worker/SHA256SUMS.txt`.

Original / source evidence: [E135](#e135), [E136](#e136)

Recorded Phase-B reproductions: [E047](#e047)

### B-S33: A06/A07 reproduction requires path staging or explicit path adaptation

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

A06 audit ZIP omits sibling PHASE_A_BLIND_AUDIT expected by source. A07 many scripts hardcode a historical Windows PAY path. Mathematical tests can be replayed by staging frozen bytes or adding configurable paths; as-delivered launch instructions are not generally relocatable.

Required interpretation/action: Add explicit --root/--output and documented dependency versions; preserve input/source hashes and record any adapter separately.

Original claim labels: `A06 README run instructions`; `A07 hardcoded PAY paths`.

Original / source evidence: [E084](#e084) (archived lines 7,8,19), [E110](#e110) (archived lines 18), [E101](#e101) (archived lines 17,19,21,22,23,24,25,26,27,28,29,30,31,32,33,43)

### B-S34: A01 source-exposure timing limits blind-plan independence

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

A01 explicitly acknowledges source-code exposure before formal attack plan; the preserved plan claims only before executing author checkers. This does not erase independent implementation but prevents stronger claim that all source was unseen before planning.

Required interpretation/action: Describe actual exposure boundary and retain plan timestamp caveat; do not infer system-level/model independence.

Original claim labels: `A01 meta-audit source-code exposure before formal plan`.

Original / source evidence: [E051](#e051) (archived lines 243), [E052](#e052) (archived lines 1)

### B-SD01: D-shift omitted in initial physical encoding

Alias: `DUPLICATE_OF_B-AT04`. Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Original claim labels: `A07 bug1`.

Original / source evidence: [E097](#e097) (archived lines 86)

### B-SD02: Cross-party commutation tested on bare local matrices

Alias: `DUPLICATE_OF_B-AT04`. Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Original claim labels: `A07 bug2`.

Original / source evidence: [E097](#e097) (archived lines 87)

### B-SD03: Factor-five error in root numeric diagnostic

Alias: `DUPLICATE_OF_FIELD-009`. Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Original claim labels: `A07 bug3`.

Original / source evidence: [E097](#e097) (archived lines 89)

### B-SD04: Unreduced z powers and unscaled cubic terms in initial field code

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Required interpretation/action: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.

Original claim labels: `A07 bug4`.

Original / source evidence: [E097](#e097) (archived lines 90)

### B-SD05: Missing cross terms/conjugation/word normalization in early SOS

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Required interpretation/action: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.

Original claim labels: `A07 bug5`.

Original / source evidence: [E097](#e097) (archived lines 92)

### B-SD06: Wrong x-squared basis and omega phase in early exact SOS

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Required interpretation/action: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.

Original claim labels: `A07 bug6`.

Original / source evidence: [E097](#e097) (archived lines 22,94)

### B-SD07: Naive V E V-adjoint used as projector

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Required interpretation/action: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.

Original claim labels: `A07 bug7`.

Original / source evidence: [E097](#e097) (archived lines 97)

### B-SD08: Hadamard instead of matrix product and wrong commutator metric

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Required interpretation/action: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.

Original claim labels: `A07 bug8`.

Original / source evidence: [E097](#e097) (archived lines 99)

### B-SD09: Initial mutation detector ignored boxes and omitted M10

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Required interpretation/action: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.

Original claim labels: `A07 bug9`.

Original / source evidence: [E097](#e097) (archived lines 101)

### B-SD10: Floating evaluation of exact root endpoints created false alarm

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.

Required interpretation/action: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.

Original claim labels: `A07 bug10`.

Original / source evidence: [E097](#e097) (archived lines 103)

### B-S35: A06 corrected D-shift and tensor-factor errors are auditor history

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Report discloses initial omitted D shifts and tensor-factor ordering mistake. Earlier failing source/run artifacts are not separately preserved in A06. Final sources/receipts support corrected checks, not reconstructed history of every failed attempt.

Required interpretation/action: Record disclosure and missing intermediate receipts without treating absent history as invalid frozen theorem.

Original claim labels: `A06 meta-audit8.5/A-004/F-005`.

Original / source evidence: [E083](#e083) (archived lines 319,320,322)

### B-E01: A07 E-01b uses setting-dependent states instead of one common embedded state

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

A07 E-01b uses setting-dependent states instead of one common embedded state

Required interpretation/action: Withdraw numerical common-state claim; baseline analytic construction remains valid

Original claim labels: `A07 E-01b`; `A07 e_povm_bridge.py joint-probability section`; `A07 final report common-space numerical claim`.

Original / source evidence: [E020](#e020)

### B-E02: A07 rank-one POVM generator has rank at most5 and does not normalize at d6

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

A07 rank-one POVM generator has rank at most5 and does not normalize at d6

Required interpretation/action: Exclude invalid d6 instance; valid dimensions still refute naive direct-effect encoding

Original claim labels: `A07 E-01a d6`.

Original / source evidence: [E020](#e020)

### B-E03: Direct Fourier sum of general POVM effects need not be unitary; dilation is essential and present

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Direct Fourier sum of general POVM effects need not be unitary; dilation is essential and present

Required interpretation/action: Treat as a negative control, not a baseline defect

Original claim labels: `A07 E-01a`; `A07 rejected V E V* projector attempt`; `A01/A02/A03/A04/A05/A06 universal bridge reasoning`.

Original / source evidence: [E046](#e046), [E022](#e022)

### B-E04: Frozen §5 terse common-space proof is valid, including infinite/nonseparable local spaces, mixed/nonnormal states; no abstract commuting-POVM scope is added

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Frozen §5 terse common-space proof is valid, including infinite/nonseparable local spaces, mixed/nonnormal states; no abstract commuting-POVM scope is added

Required interpretation/action: Optional expanded explanation of the fixed common embedding and defect-projection alternative; no repair required

Original claim labels: `A07 NL-2`; `A01 universal bridge`; `A02 universal receipt`; `A03 E01/E02`; `A04 E-01/E-02`; `A05 E1`; `A06 E-001/E-002/E-003/E-004/E-006`; `H01 §6`; `H02 common-embedding rejected objection`.

Original / source evidence: [E046](#e046), [E023](#e023)

### B-E05: Compression is positive but not multiplicative; do not substitute POVM effects directly into same-party SOS products

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Compression is positive but not multiplicative; do not substitute POVM effects directly into same-party SOS products

Required interpretation/action: Rejected shortcut is not used in baseline; preserve full dilated identity then take state expectation

Original claim labels: `New Phase B cross-audit interpretation attack`.

Original / source evidence: [E021](#e021)

### B-E06: Numerical common-space tests at9d and11d use different valid complement spaces; dimension discrepancy is not mathematical disagreement

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Numerical common-space tests at9d and11d use different valid complement spaces; dimension discrepancy is not mathematical disagreement

Required interpretation/action: Record shared analytic premise and nonindependence of A04 two implementations at square-root/Halmos layer

Original claim labels: `A01/A02/A03/A05/A06 9d construction`; `A04 6d Halmos and11d reused-Halmos direct sum`.

Original / source evidence: [E046](#e046)

### FIELD-001: Largest root and positive real algebraic embedding are valid

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

p has six real roots; exactly one above 3 and none above 31/10. s=A(mu)/B(mu)>0 at that root; positive u and the sector select zeta=exp(i*pi/10). Fresh Bezout certificate proves B is nonzero at all roots. Twelve real (mu,u-sign) embeddings were examined, with s sign determined by A/B.

Required interpretation/action: Retain theorem and root wording. Add portable exact sign witness to regression evidence.

Original claim labels: `A02:B-001/B-002/B-003`; `A03:B01/B02`; `A05:PB-B01/PB-B02`; `A06:B-001..B-006`; `A07:B-01..B-08`; `H01:§3`; `H02:root/embedding attack`.

Original / source evidence: [E129](#e129), [E128](#e128), [E130](#e130)

Recorded Phase-B reproductions: [E029](#e029), [E027](#e027)

### FIELD-002: Irreducibility is not required for these exact-zero certificates

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Every reduction relation holds at the stated actual numbers. Evaluation is a homomorphism, so formal zero implies actual zero even without proving the quotient a field. Main verifier uses only rational divisions. The new B inverse is explicitly checked, so elimination also has no unverified inversion.

Required interpretation/action: Reject requests to add irreducibility as a missing load-bearing theorem assumption; optional expository clarification only.

Original claim labels: `A05:dependency analysis`; `H01:§3`; `H02:§3`.

Original / source evidence: [E129](#e129), [E128](#e128), [E132](#e132)

### FIELD-003: Strict reality and positivity of all fourteen weights survives a non-box oracle

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

All imaginary coordinates are exactly zero. Fresh univariate elimination plus Sturm–Tarski determines signs without frozen embedding boxes or prior interval code. All weights and matching D pivots exceed 1/3000; minimum is id 9:1, strictly between 3584887/10^10 and 3584888/10^10. Fraction-only reimplementation independently agrees on 210 sign comparisons.

Required interpretation/action: Retain strict positivity claim. Cite exact sign or rational bounds, never numerical spectra as proof.

Original claim labels: `A01:positivity`; `A02:D-001/D-002/D-005`; `A03:D01`; `A05:PB-D01`; `A06:D`; `H01:§5`; `H03:negative H/LDL sign`.

Original / source evidence: [E130](#e130), [E127](#e127)

Recorded Phase-B reproductions: [E029](#e029), [E027](#e027), [E024](#e024)

### FIELD-004: Gram and compact weights coincide, so repeated pivots are not independent sign votes

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

All fourteen D values are the compact weights. H=LDL* and conjugated EL columns are an additional serialized data-path consistency check, not new positivity facts. Five small H blocks are positive definite, whereas arbitrary 81-row E embeddings yield a positive-semidefinite total Gram.

Required interpretation/action: Keep Gram as auxiliary structural/regression coverage. Do not count its fourteen pivots as independent positivity evidence.

Original claim labels: `A02:D-003/D-004`; `A03:D02/C02`; `A05:PB-D02/PB-D03`; `A06:M3`; `A07:D-02/NL-3/N1`; `H01:§5`.

Original / source evidence: [E130](#e130), [E127](#e127), [E126](#e126), [E125](#e125)

Recorded Phase-B reproductions: [E028](#e028)

### FIELD-005: Nonconsecutive block labels are benign

Alias: `DUPLICATE_OF_B-S15`. Labels 1,6,7,8,9 identify five blocks of sizes 2,4,3,3,2. Cardinality does not require consecutive IDs.

Original claim labels: `A06:NLB-4`.

Original / source evidence: [E126](#e126), [E127](#e127), [E128](#e128)

### FIELD-006: Historical candidate status is a stage marker

Alias: `DUPLICATE_OF_B-S14`. EXACT_IDENTITY_PASSED_POSITIVITY_NOT_YET_CERTIFIED records the candidate discovery stage; the separate final positivity certificate is rechecked. No checker trusts the status flags.

Original claim labels: `A06:NLB-3`; `A05:PB-D04`.

Original / source evidence: [E126](#e126), [E127](#e127)

### FIELD-007: A07 numerical positivity cannot support a rigorous independent sign verdict

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

cd_noncommutative_and_positivity.py uses mpmath 50 dps but starts XN from binary float MU; it evaluates signs numerically and converts to complex. It contains no rigorous interval sign engine. Its claim that positivity was numerically certified and supported by finite representation PSD is too strong. Fraction was available in its own harness, so this was not a demonstrated hard stop. Author replay supplies rigorous positivity but is correlated evidence.

Required interpretation/action: Downgrade A07 D-01 to numerical diagnostic; retain author replay separately. Correct audit completeness/independence language. Central gap closed by other exact evidence and fresh Phase B sign oracle.

Original claim labels: `A07:D-01`; `A07:FINAL §3.3/§8`.

Original / source evidence: [E130](#e130), [E127](#e127), [E108](#e108), [E115](#e115), [E098](#e098)

Recorded Phase-B reproductions: [E029](#e029)

### FIELD-008: A07 root mutation did not re-evaluate the coefficient embedding

Alias: `DUPLICATE_OF_B-S20`. M13 changes target MU while precomputed MONO remains at MU_TRUE. It tests a constant target shift, not a field-conjugate certificate. i_exhaustion_gate.py also incorrectly calls a smaller root a weaker bound. The algebraic identity remains valid at compatible cubic roots; positivity fails there.

Original claim labels: `A07:N2`; `A07:M-D`; `A07:M13`.

Original / source evidence: [E130](#e130), [E129](#e129), [E112](#e112), [E110](#e110), [E122](#e122)

Recorded Phase-B reproductions: [E029](#e029), [E027](#e027)

### FIELD-009: A07 first root script omitted a factor five in A squared

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

The original numeric/remainder probe used 5*(t^3-4t-4)^2 rather than 25*(...)^2 and produced spurious residuals. Its earlier symbolic A^2-5B^2 line was correct. The correction source and receipt repair the test.

Required interpretation/action: Preserve both failed/corrected artifacts; do not attribute the false alarm to the theorem.

Original claim labels: `A07:I-02 bug 3`; `A07:B-01/B-04 correction`.

Original / source evidence: [E129](#e129), [E102](#e102), [E103](#e103), [E113](#e113), [E114](#e114)

### FIELD-010: A07 treated a displayed decimal prefix as a 50-digit equality

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

The printed mu ends before the exact root decimal, so a 10^-50 comparison against the prefix fails by approximately 2.95e-49. The correction correctly recognizes truncation.

Required interpretation/action: Preserve correction; no change to ellipsis-marked theorem decimal needed.

Original claim labels: `A07:B-02 correction`.

Original / source evidence: [E128](#e128), [E103](#e103), [E114](#e114)

### FIELD-011: A05 initially expected rejection of a valid coarse u enclosure

Alias: `DUPLICATE_OF_B-S28`. An alleged leakage mutation used [3.8,3.81], which genuinely encloses positive u. Final source uses leaking [3.8,3.803], while meta_audit.py retains [3.8,3.81] as a positive control.

Original claim labels: `A05:positivity development_run_2`; `A05:PB-G02`.

Original / source evidence: [E130](#e130), [E076](#e076), [E072](#e072), [E073](#e073)

### FIELD-012: A05 positivity development had missing reverse subtraction

Alias: `DUPLICATE_OF_B-S28`. Initial R class lacked __rsub__, causing TypeError before the embedding identities completed. Final source implements it and has clean receipts.

Original claim labels: `A05:positivity development_run_1`.

Original / source evidence: [E075](#e075), [E072](#e072)

### FIELD-013: A07 independence caveat about supplied checkers is valid and already disclosed

Alias: `DUPLICATE_OF_B-S30`. verify_sos14 imports verify_independent arithmetic, reducer, positivity and physical checks. This is one underlying author engine, though two certificate data paths. PROOF §7 already explicitly discloses the reuse.

Original claim labels: `A07:NL-1/M-A`.

Original / source evidence: [E133](#e133), [E132](#e132), [E128](#e128)

### FIELD-014: A06 other-root positivity sensitivity was numerical, not exact

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

chk_root_sensitivity.py uses 50-digit mpmath on the three roots with fixed positive sqrt5. Counts 6 and 5 negative weights at the two smaller compatible roots agree with fresh exact signs; it did not certify root sign comparisons.

Required interpretation/action: Keep as noncertifying diagnostic; Phase B exact branch census upgrades the scientific coverage.

Original claim labels: `A06:N3`; `A06:R15`.

Original / source evidence: [E130](#e130), [E092](#e092), [E095](#e095)

Recorded Phase-B reproductions: [E029](#e029)

### FIELD-015: A06 Gaussian algebraic inversions verify units explicitly

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

The report sometimes uses formal nonzero tests, which alone need not establish nonzero actual values in an arbitrary quotient. But F.inv solves the multiplication system and checks self*out==ONE; actual evaluation therefore proves every inverted element nonzero without irreducibility.

Required interpretation/action: Do not manufacture a division gap. Explain the explicit unit-identity check when describing A06 arithmetic.

Original claim labels: `A06:B-006`; `A06:cglib F.inv`.

Original / source evidence: [E129](#e129), [E085](#e085)

### FIELD-016: Phase-B sign crosscheck first attempt compared different zero polynomial serializations

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Fraction tuple () represents zero while SymPy all_coeffs() uses [0]. A serialization equality assertion aborted before the meta-check verdict. No sign result was accepted; correction normalizes both representations and the full rerun passes 210 checks.

Required interpretation/action: Preserve attempt1 source and stderr; include in run provenance.

Original claim labels: `FIELD-META-ATTEMPT1`.

Original / source evidence: None listed for this row; consult its original evidence and lane report.

Recorded Phase-B reproductions: [E026](#e026), [E027](#e027)

### FIELD-017: Fresh attainment quotient is tied to the physical real embedding and nonzero state

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Independent cross-map verifies all 576 quartic-u/cubic-mu basis products, 24 conjugations and 24 serialized basis maps. Exact actual-root signs give d>4, five positive cleared state components and positive norm; phase identities and sector fix zeta.

Required interpretation/action: Cite the field crossreview alongside attainment exact_linkage. Rerun if reviewed source hash changes.

Original claim labels: `ATTAINMENT:exact_linkage`.

Original / source evidence: [E130](#e130), [E129](#e129), [E128](#e128)

Recorded Phase-B reproductions: [E025](#e025)

### NC-001: Author checkers share one arithmetic and normalizer implementation

Alias: `DUPLICATE_OF_B-S30`. verify_sos14 imports ZERO,MU,load_scalar,canon,star,word_product,make_bell,interval_basis,positive and physical checking from verify_independent. Historical kill_tests imports the same engine. These executions are not independent arithmetic/normal-form votes. PROOF explicitly discloses compact arithmetic reuse.

Original / source evidence: [E133](#e133), [E132](#e132)

### NC-002: A01 pre-plan source exposure limits procedural blindness

Alias: `DUPLICATE_OF_B-S34`. A01 META-01 admits reading supplied checker source before the formal pre-check plan. It still writes a distinct Groebner table and direct-event strategy implementation.

Original / source evidence: [E051](#e051), [E050](#e050)

### NC-003: A06 modular checks reuse exact multiplication table and normalizer

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

MULTI is derived directly from cglib_audit.MULT; modular Bell/word products call L.canon,L.star,L.wmul. Changing Fraction scalars to residues breaks rational-accumulation correlation, not relation-table or word-semantics correlation.

Required interpretation/action: Credit modular corruption controls only with shared-table/shared-normalizer qualifier. A03/A04 independent prime specializations and fresh Fp2 matrices supply different correlation controls.

Original / source evidence: [E089](#e089), [E085](#e085)

### NC-004: A06 claimed abelianization control is not abelianization

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

commutative_canon counts each (r,k) occurrence rather than adding exponents and drops multiplicities; it also orders generators incompatibly with its target. It maps U0*U0 to U0. True quotienting of a genuine identity must preserve that identity.

Required interpretation/action: Withdraw control_commutativisation_detected as evidence. Replace with injected noncommutative commutator that vanishes after proper abelianization. No frozen scientific edit.

Original / source evidence: [E089](#e089), [E094](#e094)

Recorded Phase-B reproductions: [E033](#e033)

### NC-005: A06 concrete word evaluator reverses factor order

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

word_matrix multiplies each factor on the left. In a two-dimensional exact-order-five numerical representation, a synthetic U0 U2 word differs from intended order by 0.6633436854000504. All 164 frozen raw monomials contain at most one operator per party and are unaffected. The separate high-precision matrix script repeats the same left-multiplication pattern and shares this generic-order limitation.

Required interpretation/action: Change left multiplication to right multiplication in future auditor code and add same-party synthetic-word tests. Keep frozen concrete SOS diagnostic, but do not credit the evaluator as a generic order-semantic check.

Original / source evidence: [E088](#e088), [E087](#e087)

Recorded Phase-B reproductions: [E034](#e034)

### NC-006: 17, 273, 337 and 1681 word counts measure different sets

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

17 is final nonzero support after exact cancellation; 273 is actual touched union; H01 second route retains 64 zero Fourier-target slots giving 337; 1681 is full Q*Q Gram universe. A06 sparse W removes exact zeros but separately records 273 touched words.

Required interpretation/action: Do not treat count differences as omitted residuals. Keep labels distinguishing touched, surviving, zero-target and full-basis sets.

Original / source evidence: [E093](#e093), [E096](#e096), [E138](#e138), [E128](#e128)

### NC-007: A07 archived rational SOS path is a failed implementation

Alias: `DUPLICATE_OF_B-S25`. Archived rational RHS loops only each monomial and adds coef at word*word-adjoint, omitting weights, coefficient products/conjugation and cross terms. Its own receipt is FAIL with one RHS word and 17 residuals. This is not a failed baseline certificate.

Original / source evidence: [E107](#e107), [E118](#e118), [E099](#e099)

Recorded Phase-B reproductions: [E031](#e031), [E032](#e032)

### NC-008: A07 adjoint probe crashes after partial useful numeric output

Alias: `DUPLICATE_OF_B-S25`. Four variant computations finish and distinguish coefficient conjugation and cross terms, but final display loop destructures a word as w,_ and crashes on the empty word. No completed end-to-end run or exact proof credit is justified.

Original / source evidence: [E104](#e104), [E117](#e117)

### NC-009: A07 earlier cyclotomic construction bugs are historical harness defects

Alias: `DUPLICATE_OF_B-SD04`. Reported earlier unreduced z^18/z^19 and unscaled cubic additions were field-engine defects. Final archived routines visibly perform proper reduction/scaling, but those old source versions are not all preserved.

Original / source evidence: [E097](#e097), [E107](#e107)

### NC-010: A07 earlier basis and wrap-phase bugs corrected in final integer path

Alias: `DUPLICATE_OF_B-SD06`. Comments and ledger describe b=2 parsed as x instead of x^2 and omega^(-k) encoded as zeta^(-k) instead of zeta^(-4k). Final code uses repeated x multiplication and phase -4k; fresh integer replay has zero residual on 273 words.

Original / source evidence: [E097](#e097), [E106](#e106), [E116](#e116)

Recorded Phase-B reproductions: [E031](#e031)

### NC-011: A07 earlier random-unitary and cross-commutator bugs corrected

Alias: `DUPLICATE_OF_B-SD08`. Archived source documents earlier Hadamard product instead of matrix multiplication and comparison of operators instead of commutator. Final source uses q@diag and tensor commutator, with assertions.

Original / source evidence: [E108](#e108), [E097](#e097)

### NC-012: A07 C06 overstates direct SOS matrix dimension coverage

Disposition: `MISREPORT_OR_REJECTED_FINDING`.

Only d=5,10,15 (nine cases) evaluate SOS. d=20,25 (six cases) assign residual=NaN and test Bell minimum eigenvalues and generator relations. The ledger labels C06 identity tests at all five dimensions. CD receipt is a tail, not full transcript.

Required interpretation/action: Separate nine actual SOS evaluations from six Bell-only diagnostics; retain max direct residual 2.0589752126226678e-11 as numerical, not exact evidence.

Original / source evidence: [E108](#e108), [E115](#e115), [E097](#e097)

### NC-013: A07 compact verification does not establish Gram-data consistency

Alias: `DUPLICATE_OF_B-S24`. N1 says compact anticommutator checking covers the same Gram parametrization, but only Q basis matching and supplied Gram checker replay are independent of its compact route. No independent E,H,L,D-to-R equality was checked by A07.

Original / source evidence: [E097](#e097), [E098](#e098)

### NC-014: A01 relabel negative control rejects duplicate support before identity

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

A01 generator_relabel case is rejected for a duplicate polynomial word, so that case tests schema uniqueness, not necessarily the semantic identity response to a support-preserving relabel.

Required interpretation/action: Limit credit to parser detection. A02 nonduplicate relabel and A05 full-R relabel separately test semantics.

Original / source evidence: [E055](#e055)

### NC-015: A03 and A04 initial malformed fixtures abort before controls

Alias: `DUPLICATE_OF_B-S26`. Both initially assume a dense first polynomial coefficient has a zero numerator. StopIteration prevents malformed-case execution. Later fixtures choose existing zero coordinates.

Original / source evidence: [E058](#e058), [E059](#e059), [E064](#e064), [E066](#e066)

### NC-016: A04 exhaustive coefficient sweep is exact delta testing

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

After timeout, 164 controls evaluate exact perturbation deltas, with one full mutated-term expansion crosscheck per square. These are not 164 full end-to-end verifier invocations. Formula includes four linear cross terms plus 2*d*delta^2.

Required interpretation/action: Credit exact algebraic sensitivity sweep with correct scope; retain timeout history; no baseline defect.

Original / source evidence: [E062](#e062), [E064](#e064), [E067](#e067)

### NC-017: A04 first new-support author rejection was invalid invocation

Alias: `DUPLICATE_OF_B-S27`. Initial harness supplied positional JSON to --root verifier; nonzero exit did not establish mathematical rejection. Corrected invocation repeats run and reaches ArithmeticError residual rejection.

Original / source evidence: [E064](#e064), [E068](#e068), [E069](#e069)

### NC-018: Shared algebraic presentation does not require irreducibility for zero implication

Alias: `DUPLICATE_OF_FIELD-002`. All exact engines use the printed actual-number relations. A zero produced solely by sound polynomial identities evaluates to zero in the actual embedding whether or not the quotient basis is minimal/faithful. Branch and positivity remain separate obligations.

Original / source evidence: [E128](#e128), [E074](#e074)

### NC-019: Same-party noncommutation preserved by all inspected normalizers

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Stack separation, adjacent cross-party interchange, repeated run contraction, and expanded-letter representations all preserve local relative order and only reduce equal-generator powers mod five. Fresh test exhausts 0..4 factors over 16 nonzero syllables plus 5000 long/cancellation cases.

Required interpretation/action: No scientific normalizer repair proposed. Finite tests supplement direct source/analytic soundness; do not claim formal verification.

Original / source evidence: [E132](#e132)

Recorded Phase-B reproductions: [E039](#e039)

### NC-020: Fresh Fp2 matrices independently break field and word implementation correlation

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

102 Hermitian-unitary matrix specializations at eight primes use actual Frobenius conjugation, independent direct scalar evaluation, literal-event spectral projectors, no quotient arithmetic and no word reduction. Baseline exact residual zero; each of four targeted corruptions detected in all 102.

Required interpretation/action: Accept as exact finite-characteristic correlation control, not characteristic-zero proof or positivity evidence.

Original / source evidence: [E007](#e007)

Recorded Phase-B reproductions: [E041](#e041)

### NC-021: Fresh matrix-control initial seed accidentally commuted

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Initial generator sampler asserted noncommutation on a random finite-field pair that accidentally commuted. It stopped before issuing baseline verdict. Final sampler rejects such a fixture and deterministically advances seed.

Required interpretation/action: Preserve failed attempt; count only accepted noncommuting cases with recorded final seed. This is fixture coverage, not certificate failure.

Original / source evidence: [E006](#e006), [E040](#e040)

Recorded Phase-B reproductions: [E041](#e041)

### NC-022: Fresh generic order-control initial fixture accidentally commuted

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

All normalizer comparisons completed, then random negative-control matrices commuted and assertion correctly stopped the run. Replaced with fixed visibly noncommuting matrices; repeated entire test.

Required interpretation/action: Count final full successful run only; retain failed fixture transcript.

Original / source evidence: [E005](#e005), [E038](#e038)

Recorded Phase-B reproductions: [E039](#e039)

### NC-023: Fresh universal bridge cross-review found no new route

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Reviewed V*V-only rewrite, typed block structure, fixed common J and normalized positive-functional pullback. Replayed formal W*=W,W^2=I and exact positive compression-defect example; no extra VV*=I or multiplicative-compression assumption enters.

Required interpretation/action: No bridge change requested from NC cross-review; analytic reasoning and finite controls remain distinct.

Original / source evidence: [E003](#e003), [E002](#e002), [E001](#e001), [E046](#e046)

Recorded Phase-B reproductions: [E037](#e037), [E036](#e036)

### NC-024: A07 abandoned modular-size bound aborts and lacks valid coordinate bound

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Size receipt aborts at the 4300-digit integer-string cap after reporting the LCM. The unexecuted proposed bound treats L times residual as a rational integer, ignores basis-coordinate versus embedding magnitude and x-squared size, and does not correctly justify triple-product denominator clearing. A concrete weighted coefficient product retains denominator 5 after multiplying by L. Final A07 proof instead uses correct L cubed scaling.

Required interpretation/action: Exclude abandoned size-bound route from proof coverage; preserve partial structural/LCM observations only. No effect on successfully replayed final integer proof.

Original / source evidence: [E105](#e105), [E119](#e119)

Recorded Phase-B reproductions: [E035](#e035)

### B-AT01: Literal probability convention and full target linkage survive

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Accept exact event-wise target identification, local bound2, D shifts and Fourier sign; no scientific revision.

Original claim labels: `A01:A-01/A-02`; `A02:A-001..A-005`; `A03:A01..A03`; `A04:A-01..A-04`; `A05:A1/A2`; `A06:A-001..A-005`; `A07:A-01..A-07`; `H01:§2/events_and_fourier`.

Original / source evidence: [E018](#e018), [E128](#e128), [E130](#e130)

### B-AT02: A06 NLB-5 labels correct standard normalization a defect

Alias: `DUPLICATE_OF_B-S16`. Reject defect classification; k=0,1 is correct stated standard normalization. Summing reflected pairs through k=4 doubles the functional.

Original claim labels: `A06:NLB-5`; `A06:A-003`.

Original / source evidence: [E018](#e018), [E128](#e128), [E130](#e130)

### B-AT03: Full25-dimensional exact strategy and all28 saturation vectors survive

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Accept exact physical attainer, legal normalization, gamma linkage and full-coordinate saturation; no theorem change.

Original claim labels: `A01:F-01..F-03`; `A02:F-001..F-006`; `A03:F01..F03`; `A04:F-01/F-02/M-02`; `A05:F1/F2/PB-F01/PB-D05`; `A06:F-001..F-006`; `A07:F-01..F-05`; `H01:§7/exact_attainment`.

Original / source evidence: [E018](#e018), [E019](#e019), [E128](#e128), [E130](#e130)

### B-AT04: A07 first strategy harness omitted D shifts and mis-tested cross-party commutation

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Preserve first failed attempt, discard its operator mismatch as auditor-generated; corrected v2 reproduces attainment.

Original claim labels: `A07:F-01/F-02 first attempt`; `A07:report§7 own bugs`.

Original / source evidence: [E109](#e109), [E120](#e120), [E017](#e017), [E128](#e128), [E130](#e130)

### B-AT05: A07 generic tensor-order error hidden by exact symmetry of optimizer fixture

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Repair A07 generic build_B odd-edge Kronecker ordering and add generic event-matrix negative control. Keep its special-fixture attainment result:625 entries agree exactly.

Original claim labels: `A07:F-02/F-04/F-05`; `NEW:generic tensor-placement meta-test`.

Original / source evidence: [E016](#e016), [E128](#e128), [E130](#e130)

### B-AT06: A06105/400 supplementary random samples are incomplete purported PVMs

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Replace first-five-rank-one truncation by complete outcome grouping; validate completeness before recording samples. Discount105 original invalid samples.

Original claim labels: `A06:H-002`; `A06:chk_povm_bridge random-search branch`.

Original / source evidence: [E014](#e014), [E128](#e128), [E130](#e130)

### B-AT07: A07 product-state and fixed-measurement searches have sharply limited falsification power

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Describe searches accurately: product pure states; product mixed rho⊗rho;400 product-state phase trials; hill climb only real Schmidt amplitudes at fixed Fourier measurements. Retain12 generic spectral tests.

Original claim labels: `A07:H-01`.

Original / source evidence: [E111](#e111), [E128](#e128), [E130](#e130)

### B-AT08: A03 optimizer precision-loss and highest floating overshoot are properly limited diagnostics

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Retain eight failed BFGS starts and later derivative-free recovery distinctly; highest exact-binary-float phase endpoint lies below μ by1.75588767996e-16 at70/110 digits.

Original claim labels: `A03:H03/H06/M04`.

Original / source evidence: [E008](#e008), [E058](#e058), [E128](#e128), [E130](#e130)

### B-AT09: A04 exact-rational envelopes correctly cover nearby physical representatives

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Accept all six exact rational envelopes, independently recomputed with Gaussian integers/full tensor Bell matrices; minimum certified gap9.86874822834e-16.

Original claim labels: `A04:H-02/H-04`.

Original / source evidence: [E010](#e010), [E009](#e009), [E128](#e128), [E130](#e130)

### B-AT10: A05 strongest apparent excess is explained by nonunitary stored bases and strengthened by exact enclosure

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Accept original90/130-digit repaired-candidate diagnosis with its caveat. New rational physical representative has rigorous gap≥3.3512604648438227e-21 and correction bound1.65e-76.

Original claim labels: `A05:H1/H2/H3/H4/H5/STR-M8`.

Original / source evidence: [E077](#e077), [E011](#e011), [E128](#e128), [E130](#e130)

### B-AT11: A06 optimizer omits termination/candidate evidence and overstates search scope

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Record all31 terminations, preserve candidate arrays, label finite rank-one-PVM chart search. Fresh replay:0/31 success, best3.0157104755226802; repaired rational representative has gap≥1.1934973389758194e-15.

Original claim labels: `A06:H-004`; `A06:H-007`.

Original / source evidence: [E013](#e013), [E012](#e012), [E128](#e128), [E130](#e130)

### B-AT12: Numerical SDP/non-SDP evidence cannot be counted as universal certification

Disposition: `MISREPORT_OR_REJECTED_FINDING`.

Accept A04 ADMM as independent numerical diagnostic only (81 words,1681 moments, residual7.83e-14). Reject A06 claim random scans/local maximization are representation-independent upper-bound checks or strictly stronger than SDP. Exact independently verified SOS is a valid supersession reason.

Original claim labels: `A04:H-03`; `A05:H6`; `A06:H-007`; `A01:META-02`.

Original / source evidence: [E070](#e070), [E063](#e063), [E128](#e128), [E130](#e130)

### B-AT13: Historical lower-bound and kill-test evidence has limited independent ancestry

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Treat H02 as historical report, H03 as author-engine mutation source. H01 raw code supplies separate exact implementation, but shares algebraic relations/target definition. Do not count this as fresh full-theorem independent discovery.

Original claim labels: `H02:§3/§4/§5/T5/T6`; `H03:physical state and phase controls`.

Original / source evidence: [E048](#e048), [E049](#e049), [E128](#e128), [E130](#e130)

### B-AT14: A0649-digit check actually compares a binary64 prefix

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Replace float conversion/startswith with retained arbitrary-precision root string and explicit digit check; downrate original claimed49-digit test.

Original claim labels: `A06:H-006`.

Original / source evidence: [E090](#e090), [E128](#e128), [E130](#e130)

### B-AT15: A06 full-coordinate check uses a valid explicit leakage guard

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Accept check despite only accumulating diagonal entries: it separately rejects every nonzero individual off-diagonal contribution through B_sends_diagonal_to_diagonal and gates exit on that flag.

Original claim labels: `A06:F-003`.

Original / source evidence: [E086](#e086), [E018](#e018), [E128](#e128), [E130](#e130)

### B-AT16: Valid numerical searches supply falsification diagnostics only

Disposition: `BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT`.

Retain valid PVM/POVM spectra and near-optimal searches as convention/falsification checks; never infer a global or dimension-independent upper bound from them.

Original claim labels: `A01:H-01..H-04`; `A02:H-001..H-004`; `A03:H01/H02/H04/H05`; `A04:H-01`; `A06:H-001/H-003/H-005/H-008`.

Original / source evidence: [E018](#e018), [E128](#e128), [E130](#e130)

### B-AT17: A07 first-five truncation makes all d6/7 purported projective samples incomplete

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Discount150 trials each at d6 and d7 as invalid measurements; group every basis column into five outcomes and validate completeness. Distinct from benign product-state restriction B-AT07.

Original claim labels: `A07:H-01 random projective trials`.

Original / source evidence: [E015](#e015), [E111](#e111) (archived lines 5,2,–,6,7,;, ,b,a,s,i,s,5,6,–,5,9,;, ,s,e,l,e,c,t,i,o,n,6,4,–,6,7)

### B-CO01: Phase-B ledger merger initially expected status instead of terminal_status

Disposition: `AUDITOR_OR_HARNESS_DEFECT`.

Metadata assembly aborted before writing a merged attack ledger because schema lane uses terminal_status while other lanes use status. The explicit missing-status assertion failed closed. Corrected merger accepts either named field and validates all52 terminal routes; scientific scripts and results unchanged.

Required interpretation/action: Retain failed assembly attempt and corrected merger; no scientific or baseline change.

Original / source evidence: [E004](#e004), [E030](#e030)

## Evidence index: original path and byte identity

All hashes are SHA-256. These are exact paths inside the final Phase-B ZIP. A receipt path identifies a historical record; it does not assert fresh v0.1.1 execution.

<a id="e001"></a>
**E001** — `outputs/INDEPENDENT_CHECKS/bridge/compression_product_attack.py`  
SHA-256: `e25f050ee86b9ef49abf02fd7dbb240ce81bde167fb62608eaac0a18611d3bb8`

<a id="e002"></a>
**E002** — `outputs/INDEPENDENT_CHECKS/bridge/exact_common_space.py`  
SHA-256: `2b1cad53a8acac603b1655ae0a29363cb2dbe73d096da4003891713c0c3e463c`

<a id="e003"></a>
**E003** — `outputs/INDEPENDENT_CHECKS/bridge/formal_isometry_bridge.py`  
SHA-256: `7544f6649130787b7383bd5d31285a3ad86a5085eb2c232a954ccc948d2ac1ff`

<a id="e004"></a>
**E004** — `outputs/INDEPENDENT_CHECKS/coordinator/merge_attacks.attempt1.py`  
SHA-256: `e20cdd4d52e5e9f8057831201c593c437bdd3975c52bbafbe8a3106fb5079de0`

<a id="e005"></a>
**E005** — `outputs/INDEPENDENT_CHECKS/nc/cross_audit_normal_forms.attempt1.py`  
SHA-256: `d51359ce7d70830c60155516b52a674b6784c9f649378f0b39fdcb002874cda2`

<a id="e006"></a>
**E006** — `outputs/INDEPENDENT_CHECKS/nc/finite_field_matrix_attack.attempt1.py`  
SHA-256: `1bd7b57941f5e50c13ab6567877c8eec7b93f5ef69f049cdd6b7fe701b8bd74e`

<a id="e007"></a>
**E007** — `outputs/INDEPENDENT_CHECKS/nc/finite_field_matrix_attack.py`  
SHA-256: `0f95bf95784a37088110795385bdf3ba5a98702d645f9dd50293ae48424b1b40`

<a id="e008"></a>
**E008** — `outputs/RUN_RECEIPTS/attainment/a03_near_replay.json`  
SHA-256: `5dec2e298f9b7c8ba910d2f213ffb765f86f8ac4978ac00ae1f24cc00908d709`

<a id="e009"></a>
**E009** — `outputs/RUN_RECEIPTS/attainment/a04_integer_envelopes.json`  
SHA-256: `9228eea15029b951293053e618785bd282655539ccac2959204562a263bfcd74`

<a id="e010"></a>
**E010** — `outputs/RUN_RECEIPTS/attainment/a04_rational_replay.json`  
SHA-256: `c184e5588ec827445715f67aec281681797fc08c9df343c7fffd7d7549040605`

<a id="e011"></a>
**E011** — `outputs/RUN_RECEIPTS/attainment/a05_integer_envelope.json`  
SHA-256: `7b488f6e9f15179fb373c843077dcd55f5a53c7e87685cb9d647f5ed448e1458`

<a id="e012"></a>
**E012** — `outputs/RUN_RECEIPTS/attainment/a06_integer_envelope.json`  
SHA-256: `15c185874d91dc47762ea3ee170b3a2f7dbacc516ce5fa74986ca71092962709`

<a id="e013"></a>
**E013** — `outputs/RUN_RECEIPTS/attainment/a06_optimizer_replay.json`  
SHA-256: `26e5d56468f418ef59cf264211705f2339bfe71a4d5a3a7a3e83c7afb7992bde`

<a id="e014"></a>
**E014** — `outputs/RUN_RECEIPTS/attainment/a06_search_health.json`  
SHA-256: `ad1afbbc0d45c13eb7fdec058c9e1973ca652450fc1f6b81f7ce70d325a30928`

<a id="e015"></a>
**E015** — `outputs/RUN_RECEIPTS/attainment/a07_sampling_health.json`  
SHA-256: `08fd5b907c03667e618ee54353636f95233a8410195df72cd71c40723d3b7c98`

<a id="e016"></a>
**E016** — `outputs/RUN_RECEIPTS/attainment/a07_tensor_control.json`  
SHA-256: `d0abf498c7ab1c888baad7a2aef6c46fc9e6f6933810b56ca6bf507e4eb7b911`

<a id="e017"></a>
**E017** — `outputs/RUN_RECEIPTS/attainment/a07_v2_replay/stdout.txt`  
SHA-256: `ac94072f90d9cc138ad7a054b9fdf01495eb5e421bc13ede70c59435be0367e0`

<a id="e018"></a>
**E018** — `outputs/RUN_RECEIPTS/attainment/exact_linkage.json`  
SHA-256: `829b506d6b8685115cf2ce376857d2bf195c9e2231e097157720b0acd6afefeb`

<a id="e019"></a>
**E019** — `outputs/RUN_RECEIPTS/attainment/exact_linkage_replay.json`  
SHA-256: `19859259b0d22cff41afb104e52aa580854dbb8e919a6a689ae79bd30846ab11`

<a id="e020"></a>
**E020** — `outputs/RUN_RECEIPTS/bridge/a07_fixed_embedding_attack.json`  
SHA-256: `cb7a33739975ad87c65dbaf3a13687808e2b0eb706197911c704ea77eef42ef2`

<a id="e021"></a>
**E021** — `outputs/RUN_RECEIPTS/bridge/compression_product_attack.json`  
SHA-256: `e4f60d2fc2859df42da33444a45648e809e2372b254039bb3562ecb2e20cd6b3`

<a id="e022"></a>
**E022** — `outputs/RUN_RECEIPTS/bridge/exact_common_space.json`  
SHA-256: `2244bd5314ed9e840e148e0e9739616e86bfd0f607618f56c5754c3f48764409`

<a id="e023"></a>
**E023** — `outputs/RUN_RECEIPTS/bridge/formal_isometry_bridge.json`  
SHA-256: `3f6d617a247c5a4d238e31d648e59cdcfb402d53fce38968ec73dcff1b5763df`

<a id="e024"></a>
**E024** — `outputs/RUN_RECEIPTS/field/a05_bernstein_replay/positivity_bernstein_meta_results.json`  
SHA-256: `62739331838589232c86d63e6d3834d24c82928f15cdb04e5914b7a7d1ea641a`

<a id="e025"></a>
**E025** — `outputs/RUN_RECEIPTS/field/attainment_field_crossreview.json`  
SHA-256: `d8611f7b84d83b4813160f07e333c7c18bb131cf735863069b83b23811e8eac6`

<a id="e026"></a>
**E026** — `outputs/RUN_RECEIPTS/field/fraction_sign_meta.attempt1.stderr`  
SHA-256: `4ceb83c667064365510a0ec8a9197d13844b0417d39fdea72c219907823c5bf4`

<a id="e027"></a>
**E027** — `outputs/RUN_RECEIPTS/field/fraction_sign_meta.json`  
SHA-256: `157ec6b14cf7404b03b3e4c36fe0335dbc83f1a0884674e6e3afe76cf9e3fc06`

<a id="e028"></a>
**E028** — `outputs/RUN_RECEIPTS/field/gram_elimination.json`  
SHA-256: `09a161bb4405f63275f5de342323dcefcfd454cabdd10bb4a6e1c20248ae5791`

<a id="e029"></a>
**E029** — `outputs/RUN_RECEIPTS/field/sturm_tarski_weights.json`  
SHA-256: `89b225739dd7427e31e0357d77b04c4c55a47c58bcec02b4657a690577df8a89`

<a id="e030"></a>
**E030** — `outputs/RUN_RECEIPTS/merge_attacks.attempt1.stderr`  
SHA-256: `9e86785d7e087e44fa9aac7d52c4ba5680608e1da25d89c58475ea343267f2e0`

<a id="e031"></a>
**E031** — `outputs/RUN_RECEIPTS/nc/A07_exact.json`  
SHA-256: `ba24c4f9f4eb50df40f7b6cddf2e0698dd80f0ac121d755b4a7ea0896829fa1d`

<a id="e032"></a>
**E032** — `outputs/RUN_RECEIPTS/nc/A07_exact.replay_meta.json`  
SHA-256: `65f9ae6f9bfbe3263713ca4c12b2cb2125ceedec778035ceabe57aff3a4beb0b`

<a id="e033"></a>
**E033** — `outputs/RUN_RECEIPTS/nc/a06_commutativization.json`  
SHA-256: `186b3c39061ee8fa2de8637810a1430beb9455600315844aa5e2eb0f00991f0c`

<a id="e034"></a>
**E034** — `outputs/RUN_RECEIPTS/nc/a06_matrix_order.json`  
SHA-256: `b95719dd5d57494af244a6c7c17bd14646cfada22930579dc18ecf3691f8f9dc`

<a id="e035"></a>
**E035** — `outputs/RUN_RECEIPTS/nc/a07_size_bound.json`  
SHA-256: `846b4ddcb72253a98d4810c516e9b4cb5cc8890d249fde4be2b2d02747295758`

<a id="e036"></a>
**E036** — `outputs/RUN_RECEIPTS/nc/bridge_compression_review.stdout`  
SHA-256: `e4f60d2fc2859df42da33444a45648e809e2372b254039bb3562ecb2e20cd6b3`

<a id="e037"></a>
**E037** — `outputs/RUN_RECEIPTS/nc/bridge_formal_review.stdout`  
SHA-256: `3f6d617a247c5a4d238e31d648e59cdcfb402d53fce38968ec73dcff1b5763df`

<a id="e038"></a>
**E038** — `outputs/RUN_RECEIPTS/nc/cross_audit_normal_forms.attempt1.stderr`  
SHA-256: `09c3ac0768f8f22b09a5ddb69b9faab50c554ab681795762246e04120d7f1542`

<a id="e039"></a>
**E039** — `outputs/RUN_RECEIPTS/nc/cross_audit_normal_forms.json`  
SHA-256: `949e1d9f85e28f5f559676104a9679fbeda1e6f67d0bb791c547dace8ecf1109`

<a id="e040"></a>
**E040** — `outputs/RUN_RECEIPTS/nc/finite_field_matrix.attempt1.stderr`  
SHA-256: `dd44e1b21f31915e6075f4051605dd5e43ef69cd8051f411a66b52edfc221d24`

<a id="e041"></a>
**E041** — `outputs/RUN_RECEIPTS/nc/finite_field_matrix.json`  
SHA-256: `12f8100cb353e29ee7b7266f5c1a8852f57d3649c8d87526402c7f3d07185757`

<a id="e042"></a>
**E042** — `outputs/RUN_RECEIPTS/schema/auditor_component_probes.json`  
SHA-256: `c380ffa14e5a8c29cf3334735880c63e7fa215bae41d84ff3ae94e57469cf79c`

<a id="e043"></a>
**E043** — `outputs/RUN_RECEIPTS/schema/corrected_negative_controls.json`  
SHA-256: `a7b736ebdbab83b0de8542d5fa1ef7348894086bbd7b21fbb88bcb12009e0c14`

<a id="e044"></a>
**E044** — `outputs/RUN_RECEIPTS/schema/optimization_mode_attack.json`  
SHA-256: `ceb68c0a354125a02ea795c6e07f295ecd16502d47964c91fd8ce6da9bc29c8a`

<a id="e045"></a>
**E045** — `outputs/RUN_RECEIPTS/schema/schema_attacks.json`  
SHA-256: `a971cb5e488652e1c75932707e563e36c2740dc28ff1f7b7630e803d6155c3e4`

<a id="e046"></a>
**E046** — `outputs/lanes/bridge/ANALYTIC_UNIVERSAL_BRIDGE.md`  
SHA-256: `ee155d02fa03b8a006df63abe49ee512c8f79b58c1572c46cfef8664e538f7f5`

<a id="e047"></a>
**E047** — `outputs/lanes/schema/manifest_checks_resolved.json`  
SHA-256: `7aad8c93a33afb957ef8836ccbb2d749ff03d3b138fa9f23528aa9b7e1a91b99`

<a id="e048"></a>
**E048** — `work/corpus/CGLMP5_PHASE_B_FINAL/historical_pre_phase_a/H02_INTERNAL_POST_ONESHOT_VERIFICATION_RECORD.md`  
SHA-256: `e84dbd033d581fea965c2fb016218f8e6e9eb75ad7e6cc3ea64830f6a6672b02`

<a id="e049"></a>
**E049** — `work/corpus/CGLMP5_PHASE_B_FINAL/historical_pre_phase_a/H03_original_kill_tests.py`  
SHA-256: `ba178151141acaf84891ef0610b2d3027c135e08a057c62b53151f373ecac8f7`

<a id="e050"></a>
**E050** — `work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/ATTACK_LEDGER.md`  
SHA-256: `497cc0d8eb32b2e985251800617d4aaecaecaa0206d5497e2b1afe8045011bb1`

<a id="e051"></a>
**E051** — `work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md`  
SHA-256: `01a874b1cc6b957d09ad42e1db942fa49faccb4fd1a821b79fe7e9e268d1eed2`

<a id="e052"></a>
**E052** — `work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/INDEPENDENT_CHECKS/ATTACK_PLAN_PRECHECK.md`  
SHA-256: `6043c157ca87ce9aac0005bd75169129368b34f1019109e7d3725abecfb88225`

<a id="e053"></a>
**E053** — `work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/INDEPENDENT_CHECKS/concrete_representation_sos_check.py`  
SHA-256: `b0b38b62525a6822d8fb02c2e5fb94ddaa84651dc5f6cc80fed345569227a5d0`

<a id="e054"></a>
**E054** — `work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/RUN_RECEIPTS/author_checker_attack.stdout`  
SHA-256: `17647c59ea9f4afc489a7f392b7ca0831f7525f2162ed053dc5448a57a4b5600`

<a id="e055"></a>
**E055** — `work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/RUN_RECEIPTS/mutation_controls.stdout`  
SHA-256: `4e7ba372d6e25db9fcb39a5b069d78a2dfae8ec1751dfdbb9fb1326b29da3148`

<a id="e056"></a>
**E056** — `work/expanded/A02_5p6Sol_ExternalPrompt/outputs/FINAL_AUDIT_REPORT.md`  
SHA-256: `c3407f09be8c98d3da3d4392a96b2c1cf6d5545228833e2ae213b5c5b8b17190`

<a id="e057"></a>
**E057** — `work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/author_run_driver.attempt1.stderr.txt`  
SHA-256: `077e24e89e1f209f002c5944335cc99dae86ceee0834acab554b5e77ca36e9f1`

<a id="e058"></a>
**E058** — `work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/harness_revisions.md`  
SHA-256: `43337842e050cc8509d66e4f920ba036b77f2e20b77e8f71a383dc808e6c7813`

<a id="e059"></a>
**E059** — `work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/mutations.attempt1.stderr.txt`  
SHA-256: `a806a45d556d12e18e925fb817c32cc75f97d3521058388edc209ecc11377be2`

<a id="e060"></a>
**E060** — `work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/mutations.json`  
SHA-256: `ff8afa26d46a0663eb1fa80bb17566481278d8aebd95d10caf428b0b5ce0dc2f`

<a id="e061"></a>
**E061** — `work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/numerical_kill.attempt1.stderr.txt`  
SHA-256: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`

<a id="e062"></a>
**E062** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/INDEPENDENT_CHECKS/run_controls.py`  
SHA-256: `5d4d40b646fe81803077dc6e35e109932c800ba09f607336ebbf8929f019b98e`

<a id="e063"></a>
**E063** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/INDEPENDENT_CHECKS/run_npa.py`  
SHA-256: `1419003fdfe07df5c180840fa0ef201e4cfbc88206a1465affa91fc56f927c88`

<a id="e064"></a>
**E064** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/auditor_development_corrections.md`  
SHA-256: `e64ca27d2b7f82ac3525d0fb10ae7d21fc313e1155c52d1889e7ba1fd65edc05`

<a id="e065"></a>
**E065** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/author_controls.json`  
SHA-256: `f37378dd10421cdc281880ecaaf8db72deab75457fd64c830c5bb4402dbac864`

<a id="e066"></a>
**E066** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/independent_controls.initial_failed.stdout.txt`  
SHA-256: `02d3ff88ca822a2e423764ffa8dd0dc1fcb8723e5a4952bb2b53ef701ee2f52c`

<a id="e067"></a>
**E067** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/independent_controls.timed_out.stdout.txt`  
SHA-256: `093faa21e837610b29b3167e91fa51b3b985d563fe3c06fdcda6eb24caecd6fd`

<a id="e068"></a>
**E068** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.invalid_author_invocation.json`  
SHA-256: `0e4f403a390e4291782622370fe912c4fc6029fb2f0260fd9adb711013cece5b`

<a id="e069"></a>
**E069** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.json`  
SHA-256: `e4498b12d2fddd9a31e632d07ee0ddfd71dd3e54d5642abe4726e9a5fe1c4870`

<a id="e070"></a>
**E070** — `work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/npa.json`  
SHA-256: `fd05e2ec3658d46d856eec35665d333de5c512840bdb0588c58503a187e8a11d`

<a id="e071"></a>
**E071** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/FINAL_AUDIT_REPORT.md`  
SHA-256: `3912a2d0f8cc020a14a48390911037655b9f483ee316ac08b2ee0c6c06caab2e`

<a id="e072"></a>
**E072** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/independent_positivity.py`  
SHA-256: `d9bfc89945016be05c4753f9168b2801fc2ddc37145dc21323f9b31dda1bacb5`

<a id="e073"></a>
**E073** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/meta_audit.py`  
SHA-256: `0e676f89d0e98005eba88b9a5ba0c679896ed55929dba4e925f906c196249bbe`

<a id="e074"></a>
**E074** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/sos_branch/SOS_BRANCH_REPORT.md`  
SHA-256: `17f0279f294684a46784be8b9abdbc57dda4df8ac0ee94b11396f16093e3f91e`

<a id="e075"></a>
**E075** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_1.txt`  
SHA-256: `b1276f7ee0dcd7e4b82f08f35fbab3076b6aa0f9b34a05b740b5451bbf6dc735`

<a id="e076"></a>
**E076** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_2.txt`  
SHA-256: `6fae0d8e1fab33141f085f758d54a61ec2e91b3ba6cde26181d9f63a1ab041bf`

<a id="e077"></a>
**E077** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/strategy_branch/refine_candidate.json`  
SHA-256: `3dff80f210ac2bf6b8ab22cdfd6fea5922f75fed1402643fd367936c06a32f7a`

<a id="e078"></a>
**E078** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/benign_controls.json`  
SHA-256: `5c60ff75749c0d7e711513c76e2653a53fa6fe3cc66db6a338e8e7d2464f93bc`

<a id="e079"></a>
**E079** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/independent_primitives.attempt1.stderr.txt`  
SHA-256: `84fb1f1a336c4a07702a552e978411e3cecec909fff2b03c7a1f0327cdc91955`

<a id="e080"></a>
**E080** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/mutation_classifications.json`  
SHA-256: `19cb9fa537c593b99e4d96375c356db03d17d3e47f677e3ed25aa1f749e34339`

<a id="e081"></a>
**E081** — `work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/mutations.json`  
SHA-256: `1256444fa2c5981bb844db266b817af60b4e179c4aaa93e89e302241079c5a5d`

<a id="e082"></a>
**E082** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/ATTACK_LEDGER.md`  
SHA-256: `f79568eac7fee4e2d14d821d5f7474e2aab70d09b7f5372795f646c7e47cc8ef`

<a id="e083"></a>
**E083** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/FINAL_AUDIT_REPORT.md`  
SHA-256: `49bcc3e101c9d961489df289583397a6dbb2058cf574568b9ecaf10678a7eabf`

<a id="e084"></a>
**E084** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/RUN_INSTRUCTIONS.md`  
SHA-256: `613cf6e1855411dc0cef3ce4bd36d08ed55c738a1aa60657c01394ef20d7d30c`

<a id="e085"></a>
**E085** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/cglib_audit.py`  
SHA-256: `f5736db1e42d4ed4bd5f843d4ccf29e089296b63640adedd277ba7a5b0ee6822`

<a id="e086"></a>
**E086** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_attainment.py`  
SHA-256: `8600b9cc53fc4a8ff5d660460ebeffe72ec5d748d0a3308bfbafddd41a52e7e1`

<a id="e087"></a>
**E087** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_hiprecision_residual.py`  
SHA-256: `2088a73a9609480dbaa2618c1731447e8eac5cbbb63992c4b84feb8c5c5c041b`

<a id="e088"></a>
**E088** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_matrix_falsification.py`  
SHA-256: `f258ecb531ba16aafd11f7b8f822ff1dcf5d92d807d7c5b58f291d42f7b4ab06`

<a id="e089"></a>
**E089** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_negative_controls.py`  
SHA-256: `f5934f64b1058a5a9798ac3cfd6323d66483d03f0a00106c72ec6e6dd88d548d`

<a id="e090"></a>
**E090** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_numerical_kill.py`  
SHA-256: `eb2abe47fdbcff84bf39c9a40b2284e6679befaa84cd0253c3b21ac62f046750`

<a id="e091"></a>
**E091** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_operator_functional_bridge.py`  
SHA-256: `888e2449ce9c0fd1cf9696fb9e14c613e40abf107de40178168fb7092047c45d`

<a id="e092"></a>
**E092** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_root_sensitivity.py`  
SHA-256: `519c5d13a47327a204c9baac1dd7cc22c78a303915867eeca9bac060eb1d074a`

<a id="e093"></a>
**E093** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R01_chk_sos_identity.txt`  
SHA-256: `9d8af31407c657f9dbe157d8da705f3144941330302cc00cc2ef46eb861d975e`

<a id="e094"></a>
**E094** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R07_chk_negative_controls.txt`  
SHA-256: `32f5bb9a3d4120908a5fe4970b6dafebefc8c6d3bc123f2cb34ec6e9ea688474`

<a id="e095"></a>
**E095** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R15_root_sensitivity.txt`  
SHA-256: `48c13978cd31774a0d39e87fb6296d0c700a59a7bb2598f66dc82f7a3747b9e5`

<a id="e096"></a>
**E096** — `work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R17_word_counts.txt`  
SHA-256: `a0232663723642bef6301bd56466933c590897169387071fb26259878653230a`

<a id="e097"></a>
**E097** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md`  
SHA-256: `9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad`

<a id="e098"></a>
**E098** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md`  
SHA-256: `4f6465c63d7886f8823047b031021f5584fe27d3836d0435269062f6b6fa7fe0`

<a id="e099"></a>
**E099** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/C_summary.json`  
SHA-256: `87e364f4d846189e586f245debc8384cdcb9bef77526c964958c07a51234e228`

<a id="e100"></a>
**E100** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/G_summary.json`  
SHA-256: `37bfae8a5c532d3330443fa66a2c8bcb256bfe7a826ec3073250cbfd58eba40c`

<a id="e101"></a>
**E101** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/README.md`  
SHA-256: `328b4d85e1da6486add3fce95671fe72766a12372453c99557c2526c732f0db2`

<a id="e102"></a>
**E102** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/b_root_embedding.py`  
SHA-256: `77267f5eb696b963cb545597ca02ad6aae4c100b2988a061ea89b08cab6db534`

<a id="e103"></a>
**E103** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/b_root_embedding_correction.py`  
SHA-256: `1848718c2c45c5b6930d6ee9c5e5c72167b8e2f1b1ff9a2c24d43498611327a6`

<a id="e104"></a>
**E104** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_adjoint_convention_probe.py`  
SHA-256: `015f742cf327a615e9b3ca0ee76b36230297c967de62a365fee497fcbaf38c3e`

<a id="e105"></a>
**E105** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_size_analysis.py`  
SHA-256: `25b1622e6daf5826b8f5855f4bdfff0d11702bf4b148d9543125516829740bf1`

<a id="e106"></a>
**E106** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_exact_integer.py`  
SHA-256: `0bd748964bce3df7254cc5a202bd1d7e90f220acf9a05d38a7fdd1e245668c6c`

<a id="e107"></a>
**E107** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_independent.py`  
SHA-256: `b02785106edda308ffaffe72116882a696278611dd72bf5e8922e89f7ed1259f`

<a id="e108"></a>
**E108** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/cd_noncommutative_and_positivity.py`  
SHA-256: `0bb0751455ff82bac9d4dd41159b1e364ec2887485b106f8f42d4c4ee58fadef`

<a id="e109"></a>
**E109** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/f_strategy_encoding.py`  
SHA-256: `9a31b5b8f146793668c4543fe4906cae659fca4ffd8937f5349fb51b1a4c364d`

<a id="e110"></a>
**E110** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/g_mutation_controls.py`  
SHA-256: `2554ebf40dc8d8e35e9d9e0ec23872fec8b0a7096a759e0f82889e29cb5aacee`

<a id="e111"></a>
**E111** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/h_numeric_kill.py`  
SHA-256: `0a2d747fb91f6e39765c482ffed8a282130f020c1d7577f049267d8c084ffd3d`

<a id="e112"></a>
**E112** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/i_exhaustion_gate.py`  
SHA-256: `705fd5ccd2a156c43a130286b9c2496faf04e4546fb32189e87ff0f0033fadd7`

<a id="e113"></a>
**E113** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/B_receipt.txt`  
SHA-256: `b1a4666efb304aee6a96b43d8944b18beef377a521d19a2e76168fb44a55f1f8`

<a id="e114"></a>
**E114** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/B_receipt_correction.txt`  
SHA-256: `911af6085f9e841d7c02a44a48143050eb626305cad84337242a43db8d5e870b`

<a id="e115"></a>
**E115** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/CD_receipt.txt`  
SHA-256: `456e5cd4779abf2ec33e57d1b123b3658e94ae0de8acc60c82aaaf1783c7597f`

<a id="e116"></a>
**E116** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_exact_receipt.txt`  
SHA-256: `2f588309f6dcd27fb4ac09d7c4de533df6cd95209323537331506b3a62246f68`

<a id="e117"></a>
**E117** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_probe_receipt.txt`  
SHA-256: `134d8939805992fd030f62a7878e2233897c2b75be263432282404b6d2f135ed`

<a id="e118"></a>
**E118** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_receipt.txt`  
SHA-256: `462f2128142e39998c9c7b0c19ed59369b0c4a45a931d5f98564f8ae9f72d7e0`

<a id="e119"></a>
**E119** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_size_receipt.txt`  
SHA-256: `120ed3ae5df0b47f85810baec2b4ca72420620785ae5c6dbcbb484e334316756`

<a id="e120"></a>
**E120** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/F_receipt.txt`  
SHA-256: `cc3c69e520c960a914f6d724891cacf6866f4deea9e6737251ec6191ede69f2b`

<a id="e121"></a>
**E121** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/G_exact_on_M2.txt`  
SHA-256: `1950994769e142df655f7d3079547d4c58452b71732073c43a2d8116b0c724cd`

<a id="e122"></a>
**E122** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/G_receipt.txt`  
SHA-256: `815edf3d5a944b8410f3a153f024722a62b04e38ab5258c8cffc326d12dc149e`

<a id="e123"></a>
**E123** — `work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/I_exhaustion_receipt.txt`  
SHA-256: `9fc10bab112068b7f5207f5e309c67b2d126870d5ddcb027a17479a2af88f434`

<a id="e124"></a>
**E124** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/FROZEN_SOURCE_REFERENCE.md`  
SHA-256: `367d2c70cf296027826ff50f1cc621cea56ba978c028c42eb4f26f0ec7312a6d`

<a id="e125"></a>
**E125** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_KERNELS.json`  
SHA-256: `6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5`

<a id="e126"></a>
**E126** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json`  
SHA-256: `14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649`

<a id="e127"></a>
**E127** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json`  
SHA-256: `22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de`

<a id="e128"></a>
**E128** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md`  
SHA-256: `a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee`

<a id="e129"></a>
**E129** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md`  
SHA-256: `81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119`

<a id="e130"></a>
**E130** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json`  
SHA-256: `1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2`

<a id="e131"></a>
**E131** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/validate_integer_encoding.py`  
SHA-256: `d4f9c72acbc54acbbedc21132848c52260cc2aaba0b3301f0237459bef4ffb6b`

<a id="e132"></a>
**E132** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py`  
SHA-256: `8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3`

<a id="e133"></a>
**E133** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py`  
SHA-256: `90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094`

<a id="e134"></a>
**E134** — `work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_statement.py`  
SHA-256: `b94e281b07a63224b95fa2ece2482f5ed774c99fa461d51a37f0a61c8ac76d37`

<a id="e135"></a>
**E135** — `work/expanded/CGLMP5_v0.1_C001/CGLMP5_v0.1/verification/receipts/packaging_identity.json`  
SHA-256: `b603d7e0649e2907e9c01b3e75e54e3bc2e681e2d8332880c16009ccd40740ea`

<a id="e136"></a>
**E136** — `work/expanded/CGLMP5_v0.1_C001/CGLMP5_v0.1/verification/receipts/reconstruction/lower_worker/SHA256SUMS.txt`  
SHA-256: `5035433d028803c11b9da876853f1238b0753a116c2fac857c63191f3b8e2b7a`

<a id="e137"></a>
**E137** — `work/expanded/H01_Web6Pro_independent_audit/CGLMP5_independent_audit/crosscheck.py`  
SHA-256: `98600f8a694821ad10c728bb7f906150bf294688562b57c1ef11f5074a32d22b`

<a id="e138"></a>
**E138** — `work/expanded/H01_Web6Pro_independent_audit/CGLMP5_independent_audit/crosscheck_results.json`  
SHA-256: `9cec9249955ae4b77ef1ee20096cbe69fe93757c7d4aa569d50c1bec2daa0d14`


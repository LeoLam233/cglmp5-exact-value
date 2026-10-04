# Master findings ledger

Adjudication is by claim and dependency, not by auditor vote. Every row has exactly one primary class. Duplicate rows retain provenance and point to a canonical finding. The machine-readable companion retains full source paths, hashes, line spans and replay receipts. No frozen input bytes were changed.

| ID | Primary class | Finding | Theorem changes? | Disposition |
|---|---|---|---|---|
| B-S01 | CONFIRMED_NONLOAD_BEARING_DEFECT | Scalar float/Boolean coercion in standalone mathematical entrypoints | False | Require one shared strict decoder at every entrypoint; preserve frozen v0.1 bytes. |
| B-S02 | CONFIRMED_NONLOAD_BEARING_DEFECT | Duplicate JSON keys use last-value semantics in mathematical entrypoints | False | Use duplicate-key rejection for all mathematical JSON reads. |
| B-S03 | CONFIRMED_NONLOAD_BEARING_DEFECT | Compact word float/Boolean aliases accepted by equality semantics | False | Require actual integer word factors in all consumer paths. |
| B-S04 | CONFIRMED_NONLOAD_BEARING_DEFECT | Strict preflight misses Gram Q syntax | False | Add explicit required Q schema validation before mathematical comparison. |
| B-S05 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Missing scalar members pass syntax-only preflight but fail mathematical consumer | False | Document limited scope or upgrade to full required schema; do not portray preflight alone as certification. |
| B-S06 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Integer-string word schema mismatch is fail-closed | False | Choose and enforce one documented word-type schema. |
| B-S07 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Added explicit zero is mathematical no-op, storage count is not nonzero count | False | Either prohibit explicit zeros as canonical schema or label counts stored/nonzero separately. Do not require a scientific repair. |
| B-S08 | CONFIRMED_NONLOAD_BEARING_DEFECT | Theorem descriptors and proof bytes are not bound to checker PASS | False | Emit checker version, authoritative theorem identifier and verified input digests; explicitly separate annotations from enforced claims; bind frozen proof/document hashes in release wrapper. |
| B-S09 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Ignoring cached PASS flags, stored word universes and pivot enclosures is intentional | False | Keep recomputation; explicitly mark ancillary/historical fields non-authoritative. |
| B-S10 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Duplicate diagnostic term IDs are benign to algebra but weak for provenance | False | Enforce unique IDs for traceability if adopting strict schema. |
| B-S11 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Valid rescaling, common phase, summand order and unreduced rationals remain valid | False | Retain benign-control regressions alongside corruption tests. |
| B-S12 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Rejection of equivalent noncanonical words is a format scope limit | False | Document canonical encoding and distinguish semantic corruption from canonical-format rejection. |
| B-S13 | CONFIRMED_NONLOAD_BEARING_DEFECT | Dangling historical references in scientific payload | False | Mark references as historical/excluded and identify original-release paths; do not import missing code as proof premise. |
| B-S14 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Historical positivity-not-yet-certified status is not current evidence | False | Label status historical or remove stale annotation in a separately versioned package. |
| B-S15 | MISREPORT_OR_REJECTED_FINDING | Nonconsecutive block labels do not contradict five blocks | False | Reject proposed scientific repair; optional explanatory label note only. |
| B-S16 | MISREPORT_OR_REJECTED_FINDING | Correct k=0,1 convention is not a non-load-bearing defect | False | Retain standard convention; route numerical coefficient comparison to convention lane. |
| B-S17 | MISREPORT_OR_REJECTED_FINDING | A07 no-silent-coercion claim is contradicted by inspected source | False | Correct coverage to frozen-data parse only; count strong malformed-input tests from A01–A05 rather than vote counts. |
| B-S18 | AUDITOR_OR_HARNESS_DEFECT | A06 independent encoding audit is not strict | False | Replace int()/lstrip-is-digit validation with exact types/canonical strings, complete Q and fraction schemas, and executable malformed-input controls. |
| B-S19 | AUDITOR_OR_HARNESS_DEFECT | A07 sign-flip controls actually triple a coordinate | False | Correct mutators to negate; Phase B freshly ran both true sign controls and both were rejected. Prior report must call historical tests coordinate tripling. |
| B-S20 | AUDITOR_OR_HARNESS_DEFECT | A07 alternate-root control only changes target constant | False | Relabel evidence and use actual full-field alternate embeddings from root lane for branch coverage. |
| B-S21 | AUDITOR_OR_HARNESS_DEFECT | A07 exact checker exits zero even for explicit FAIL | False | Return nonzero for failed mathematical status and require receipt status/residual, not exit alone. |
| B-S22 | AUDITOR_OR_HARNESS_DEFECT | A07 aggregate mutation summary does not reproduce final all-16 claim | False | Preserve old misses, add consolidated reproducible exact/box runner and checked final summary with input/source hashes. |
| B-S23 | MISREPORT_OR_REJECTED_FINDING | A07 polynomial order and annotation-location prose are wrong | False | Correct report metadata descriptions; require field-name/location/order checks. |
| B-S24 | MISREPORT_OR_REJECTED_FINDING | A07 Gram redundancy argument overstates byte coverage | False | Mark A07 Gram/LDL as author replay/partial structural check, not independent exact Gram reconstruction; do not count redundant claims as extra independent votes. |
| B-S25 | AUDITOR_OR_HARNESS_DEFECT | A07 failed partial diagnostics must not be counted as complete successful runs | False | Retain partial records with terminal status, narrow coverage to completed steps, and provide final corrected driver receipts. |
| B-S26 | AUDITOR_OR_HARNESS_DEFECT | A03 and A04 initial mutation selectors aborted before intended checks | False | Keep failures excluded from successful coverage and regression-test fixture selection. |
| B-S27 | AUDITOR_OR_HARNESS_DEFECT | A04 argument-error rejection and partial sweeps are distinct from mathematical tests | False | Preserve exact error categories and coverage granularity; validate stderr/status alongside return code. |
| B-S28 | AUDITOR_OR_HARNESS_DEFECT | A05 development parser and arithmetic failures were corrected, not theorem failures | False | Retain exact failure scope, corrected-source hashes and independent norm/Fourier tests; do not count aborted attempts as successful evidence. |
| B-S29 | AUDITOR_OR_HARNESS_DEFECT | A01 numerical checker can falsely emit PASS with assertions disabled | False | Add optimize guard or explicit failure checks, record optimize flag, and require results to satisfy declared numerical thresholds. |
| B-S30 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Author entrypoints and several audit paths are correlated evidence families | False | Use per-node ancestry matrix, not majority PASS. Compact/Gram identical weights are one positivity object, not two independent proofs. |
| B-S31 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Hashes establish supplied byte identity, not external provenance or audit blindness | False | Keep provenance claims bounded; no theorem premise may rely on unseen history or novelty status. |
| B-S32 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Historical nested manifest mismatch is disclosed path normalization | False | Label historical manifests and required cwd; retain original→curated mapping. Do not rewrite historical hashes as if original receipts were unchanged. |
| B-S33 | AUDITOR_OR_HARNESS_DEFECT | A06/A07 reproduction requires path staging or explicit path adaptation | False | Add explicit --root/--output and documented dependency versions; preserve input/source hashes and record any adapter separately. |
| B-S34 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A01 source-exposure timing limits blind-plan independence | False | Describe actual exposure boundary and retain plan timestamp caveat; do not infer system-level/model independence. |
| B-SD01 | DUPLICATE_OF_B-AT04 | D-shift omitted in initial physical encoding | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD02 | DUPLICATE_OF_B-AT04 | Cross-party commutation tested on bare local matrices | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD03 | DUPLICATE_OF_FIELD-009 | Factor-five error in root numeric diagnostic | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD04 | AUDITOR_OR_HARNESS_DEFECT | Unreduced z powers and unscaled cubic terms in initial field code | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD05 | AUDITOR_OR_HARNESS_DEFECT | Missing cross terms/conjugation/word normalization in early SOS | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD06 | AUDITOR_OR_HARNESS_DEFECT | Wrong x-squared basis and omega phase in early exact SOS | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD07 | AUDITOR_OR_HARNESS_DEFECT | Naive V E V-adjoint used as projector | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD08 | AUDITOR_OR_HARNESS_DEFECT | Hadamard instead of matrix product and wrong commutator metric | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD09 | AUDITOR_OR_HARNESS_DEFECT | Initial mutation detector ignored boxes and omitted M10 | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-SD10 | AUDITOR_OR_HARNESS_DEFECT | Floating evaluation of exact root endpoints created false alarm | False | Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations. |
| B-S35 | AUDITOR_OR_HARNESS_DEFECT | A06 corrected D-shift and tensor-factor errors are auditor history | False | Record disclosure and missing intermediate receipts without treating absent history as invalid frozen theorem. |
| B-E01 | AUDITOR_OR_HARNESS_DEFECT | A07 E-01b uses setting-dependent states instead of one common embedded state | False | Withdraw numerical common-state claim; baseline analytic construction remains valid |
| B-E02 | AUDITOR_OR_HARNESS_DEFECT | A07 rank-one POVM generator has rank at most5 and does not normalize at d6 | False | Exclude invalid d6 instance; valid dimensions still refute naive direct-effect encoding |
| B-E03 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Direct Fourier sum of general POVM effects need not be unitary; dilation is essential and present | False | Treat as a negative control, not a baseline defect |
| B-E04 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Frozen §5 terse common-space proof is valid, including infinite/nonseparable local spaces, mixed/nonnormal states; no abstract commuting-POVM scope is added | False | Optional expanded explanation of the fixed common embedding and defect-projection alternative; no repair required |
| B-E05 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Compression is positive but not multiplicative; do not substitute POVM effects directly into same-party SOS products | False | Rejected shortcut is not used in baseline; preserve full dilated identity then take state expectation |
| B-E06 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Numerical common-space tests at9d and11d use different valid complement spaces; dimension discrepancy is not mathematical disagreement | False | Record shared analytic premise and nonindependence of A04 two implementations at square-root/Halmos layer |
| FIELD-001 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Largest root and positive real algebraic embedding are valid | False | Retain theorem and root wording. Add portable exact sign witness to regression evidence. |
| FIELD-002 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Irreducibility is not required for these exact-zero certificates | False | Reject requests to add irreducibility as a missing load-bearing theorem assumption; optional expository clarification only. |
| FIELD-003 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Strict reality and positivity of all fourteen weights survives a non-box oracle | False | Retain strict positivity claim. Cite exact sign or rational bounds, never numerical spectra as proof. |
| FIELD-004 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Gram and compact weights coincide, so repeated pivots are not independent sign votes | False | Keep Gram as auxiliary structural/regression coverage. Do not count its fourteen pivots as independent positivity evidence. |
| FIELD-005 | DUPLICATE_OF_B-S15 | Nonconsecutive block labels are benign | False | Reject the proposed defect classification; no scientific or schema change needed. |
| FIELD-006 | DUPLICATE_OF_B-S14 | Historical candidate status is a stage marker | False | Optional documentation: label the field as discovery-stage status. Do not edit the frozen scientific theorem or misclassify as invalid positivity. |
| FIELD-007 | AUDITOR_OR_HARNESS_DEFECT | A07 numerical positivity cannot support a rigorous independent sign verdict | False | Downgrade A07 D-01 to numerical diagnostic; retain author replay separately. Correct audit completeness/independence language. Central gap closed by other exact evidence and fresh Phase B sign oracle. |
| FIELD-008 | DUPLICATE_OF_B-S20 | A07 root mutation did not re-evaluate the coefficient embedding | False | Correct N2/M-D/M13 coverage and stronger/weaker wording. Replace with the exact twelve-branch census; only the three s-positive roots represent alternative mu with fixed s=+sqrt5. |
| FIELD-009 | AUDITOR_OR_HARNESS_DEFECT | A07 first root script omitted a factor five in A squared | False | Preserve both failed/corrected artifacts; do not attribute the false alarm to the theorem. |
| FIELD-010 | AUDITOR_OR_HARNESS_DEFECT | A07 treated a displayed decimal prefix as a 50-digit equality | False | Preserve correction; no change to ellipsis-marked theorem decimal needed. |
| FIELD-011 | DUPLICATE_OF_B-S28 | A05 initially expected rejection of a valid coarse u enclosure | False | Keep corrected negative and positive controls; classify original failed assertion as harness defect, not checker escape. |
| FIELD-012 | DUPLICATE_OF_B-S28 | A05 positivity development had missing reverse subtraction | False | Keep failure provenance; no mathematical consequence. |
| FIELD-013 | DUPLICATE_OF_B-S30 | A07 independence caveat about supplied checkers is valid and already disclosed | False | Count as correlated replay; no new theorem defect or undisclosed independence claim. |
| FIELD-014 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A06 other-root positivity sensitivity was numerical, not exact | False | Keep as noncertifying diagnostic; Phase B exact branch census upgrades the scientific coverage. |
| FIELD-015 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A06 Gaussian algebraic inversions verify units explicitly | False | Do not manufacture a division gap. Explain the explicit unit-identity check when describing A06 arithmetic. |
| FIELD-016 | AUDITOR_OR_HARNESS_DEFECT | Phase-B sign crosscheck first attempt compared different zero polynomial serializations | False | Preserve attempt1 source and stderr; include in run provenance. |
| FIELD-017 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Fresh attainment quotient is tied to the physical real embedding and nonzero state | False | Cite the field crossreview alongside attainment exact_linkage. Rerun if reviewed source hash changes. |
| NC-001 | DUPLICATE_OF_B-S30 | Author checkers share one arithmetic and normalizer implementation | False | Collapse supplied verifier and historical kill-test evidence into shared implementation ancestry; retain actual tests, no scientific change. |
| NC-002 | DUPLICATE_OF_B-S34 | A01 pre-plan source exposure limits procedural blindness | False | Record source exposure; do not treat its model/prompt independence as blindness proof or discard the successful independent algorithmic checks. |
| NC-003 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A06 modular checks reuse exact multiplication table and normalizer | False | Credit modular corruption controls only with shared-table/shared-normalizer qualifier. A03/A04 independent prime specializations and fresh Fp2 matrices supply different correlation controls. |
| NC-004 | AUDITOR_OR_HARNESS_DEFECT | A06 claimed abelianization control is not abelianization | False | Withdraw control_commutativisation_detected as evidence. Replace with injected noncommutative commutator that vanishes after proper abelianization. No frozen scientific edit. |
| NC-005 | AUDITOR_OR_HARNESS_DEFECT | A06 concrete word evaluator reverses factor order | False | Change left multiplication to right multiplication in future auditor code and add same-party synthetic-word tests. Keep frozen concrete SOS diagnostic, but do not credit the evaluator as a generic order-semantic check. |
| NC-006 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | 17, 273, 337 and 1681 word counts measure different sets | False | Do not treat count differences as omitted residuals. Keep labels distinguishing touched, surviving, zero-target and full-basis sets. |
| NC-007 | DUPLICATE_OF_B-S25 | A07 archived rational SOS path is a failed implementation | False | Preserve as failed development evidence; exclude from successful exact checks. Final integer source has full cross terms and succeeds on fresh replay. |
| NC-008 | DUPLICATE_OF_B-S25 | A07 adjoint probe crashes after partial useful numeric output | False | Retain partial numeric evidence only; fix display iteration and explicit exit/status reporting in future audit package. Exact integer replay is decisive separate evidence. |
| NC-009 | DUPLICATE_OF_B-SD04 | A07 earlier cyclotomic construction bugs are historical harness defects | False | Attribute to auditor, not frozen coefficient table; do not claim direct replay of unarchived old versions. Final field-gate output and independent replay are retained. |
| NC-010 | DUPLICATE_OF_B-SD06 | A07 earlier basis and wrap-phase bugs corrected in final integer path | False | Retain as auditor development defects with final successful replacement; no central repair. |
| NC-011 | DUPLICATE_OF_B-SD08 | A07 earlier random-unitary and cross-commutator bugs corrected | False | Credit final source/receipt only; do not count old failed implementations as independent confirmations. |
| NC-012 | MISREPORT_OR_REJECTED_FINDING | A07 C06 overstates direct SOS matrix dimension coverage | False | Separate nine actual SOS evaluations from six Bell-only diagnostics; retain max direct residual 2.0589752126226678e-11 as numerical, not exact evidence. |
| NC-013 | DUPLICATE_OF_B-S24 | A07 compact verification does not establish Gram-data consistency | False | Accept Gram bypass for compact theorem proof; withdraw independent Gram-consistency coverage. Other audits separately verify those data and this lane does not reopen compact proof. |
| NC-014 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A01 relabel negative control rejects duplicate support before identity | False | Limit credit to parser detection. A02 nonduplicate relabel and A05 full-R relabel separately test semantics. |
| NC-015 | DUPLICATE_OF_B-S26 | A03 and A04 initial malformed fixtures abort before controls | False | Exclude failed attempts from mutation success counts; credit corrected final receipts only. Correlated fixture misconception illustrates why receipt inspection matters. |
| NC-016 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A04 exhaustive coefficient sweep is exact delta testing | False | Credit exact algebraic sensitivity sweep with correct scope; retain timeout history; no baseline defect. |
| NC-017 | DUPLICATE_OF_B-S27 | A04 first new-support author rejection was invalid invocation | False | Use corrected receipt only; preserve invalid invocation as auditor bug, not theorem evidence. |
| NC-018 | DUPLICATE_OF_FIELD-002 | Shared algebraic presentation does not require irreducibility for zero implication | False | Do not demand irreducibility as a missing upper-bound premise; explicitly preserve common-relation dependence and defer actual-embedding proof to root lane. |
| NC-019 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Same-party noncommutation preserved by all inspected normalizers | False | No scientific normalizer repair proposed. Finite tests supplement direct source/analytic soundness; do not claim formal verification. |
| NC-020 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Fresh Fp2 matrices independently break field and word implementation correlation | False | Accept as exact finite-characteristic correlation control, not characteristic-zero proof or positivity evidence. |
| NC-021 | AUDITOR_OR_HARNESS_DEFECT | Fresh matrix-control initial seed accidentally commuted | False | Preserve failed attempt; count only accepted noncommuting cases with recorded final seed. This is fixture coverage, not certificate failure. |
| NC-022 | AUDITOR_OR_HARNESS_DEFECT | Fresh generic order-control initial fixture accidentally commuted | False | Count final full successful run only; retain failed fixture transcript. |
| NC-023 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Fresh universal bridge cross-review found no new route | False | No bridge change requested from NC cross-review; analytic reasoning and finite controls remain distinct. |
| NC-024 | AUDITOR_OR_HARNESS_DEFECT | A07 abandoned modular-size bound aborts and lacks valid coordinate bound | False | Exclude abandoned size-bound route from proof coverage; preserve partial structural/LCM observations only. No effect on successfully replayed final integer proof. |
| B-AT01 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Literal probability convention and full target linkage survive | False | Accept exact event-wise target identification, local bound2, D shifts and Fourier sign; no scientific revision. |
| B-AT02 | DUPLICATE_OF_B-S16 | A06 NLB-5 labels correct standard normalization a defect | False | Reject defect classification; k=0,1 is correct stated standard normalization. Summing reflected pairs through k=4 doubles the functional. |
| B-AT03 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Full25-dimensional exact strategy and all28 saturation vectors survive | False | Accept exact physical attainer, legal normalization, gamma linkage and full-coordinate saturation; no theorem change. |
| B-AT04 | AUDITOR_OR_HARNESS_DEFECT | A07 first strategy harness omitted D shifts and mis-tested cross-party commutation | False | Preserve first failed attempt, discard its operator mismatch as auditor-generated; corrected v2 reproduces attainment. |
| B-AT05 | AUDITOR_OR_HARNESS_DEFECT | A07 generic tensor-order error hidden by exact symmetry of optimizer fixture | False | Repair A07 generic build_B odd-edge Kronecker ordering and add generic event-matrix negative control. Keep its special-fixture attainment result:625 entries agree exactly. |
| B-AT06 | AUDITOR_OR_HARNESS_DEFECT | A06105/400 supplementary random samples are incomplete purported PVMs | False | Replace first-five-rank-one truncation by complete outcome grouping; validate completeness before recording samples. Discount105 original invalid samples. |
| B-AT07 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A07 product-state and fixed-measurement searches have sharply limited falsification power | False | Describe searches accurately: product pure states; product mixed rho⊗rho;400 product-state phase trials; hill climb only real Schmidt amplitudes at fixed Fourier measurements. Retain12 generic spectral tests. |
| B-AT08 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A03 optimizer precision-loss and highest floating overshoot are properly limited diagnostics | False | Retain eight failed BFGS starts and later derivative-free recovery distinctly; highest exact-binary-float phase endpoint lies below μ by1.75588767996e-16 at70/110 digits. |
| B-AT09 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A04 exact-rational envelopes correctly cover nearby physical representatives | False | Accept all six exact rational envelopes, independently recomputed with Gaussian integers/full tensor Bell matrices; minimum certified gap9.86874822834e-16. |
| B-AT10 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A05 strongest apparent excess is explained by nonunitary stored bases and strengthened by exact enclosure | False | Accept original90/130-digit repaired-candidate diagnosis with its caveat. New rational physical representative has rigorous gap≥3.3512604648438227e-21 and correction bound1.65e-76. |
| B-AT11 | AUDITOR_OR_HARNESS_DEFECT | A06 optimizer omits termination/candidate evidence and overstates search scope | False | Record all31 terminations, preserve candidate arrays, label finite rank-one-PVM chart search. Fresh replay:0/31 success, best3.0157104755226802; repaired rational representative has gap≥1.1934973389758194e-15. |
| B-AT12 | MISREPORT_OR_REJECTED_FINDING | Numerical SDP/non-SDP evidence cannot be counted as universal certification | False | Accept A04 ADMM as independent numerical diagnostic only (81 words,1681 moments, residual7.83e-14). Reject A06 claim random scans/local maximization are representation-independent upper-bound checks or strictly stronger than SDP. Exact independently verified SOS is a valid supersession reason. |
| B-AT13 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Historical lower-bound and kill-test evidence has limited independent ancestry | False | Treat H02 as historical report, H03 as author-engine mutation source. H01 raw code supplies separate exact implementation, but shares algebraic relations/target definition. Do not count this as fresh full-theorem independent discovery. |
| B-AT14 | AUDITOR_OR_HARNESS_DEFECT | A0649-digit check actually compares a binary64 prefix | False | Replace float conversion/startswith with retained arbitrary-precision root string and explicit digit check; downrate original claimed49-digit test. |
| B-AT15 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | A06 full-coordinate check uses a valid explicit leakage guard | False | Accept check despite only accumulating diagonal entries: it separately rejects every nonzero individual off-diagonal contribution through B_sends_diagonal_to_diagonal and gates exit on that flag. |
| B-AT16 | BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT | Valid numerical searches supply falsification diagnostics only | False | Retain valid PVM/POVM spectra and near-optimal searches as convention/falsification checks; never infer a global or dimension-independent upper bound from them. |
| B-AT17 | AUDITOR_OR_HARNESS_DEFECT | A07 first-five truncation makes all d6/7 purported projective samples incomplete | False | Discount150 trials each at d6 and d7 as invalid measurements; group every basis column into five outcomes and validate completeness. Distinct from benign product-state restriction B-AT07. |
| B-CO01 | AUDITOR_OR_HARNESS_DEFECT | Phase-B ledger merger initially expected status instead of terminal_status | False | Retain failed assembly attempt and corrected merger; no scientific or baseline change. |

## B-S01: Scalar float/Boolean coercion in standalone mathematical entrypoints

Primary class: CONFIRMED_NONLOAD_BEARING_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["H02", "A01", "A02", "A03", "A04", "A05"]; ["H02 ALG-01", "A01 G-03/N1", "A02 G-003", "A03 N1", "A04 NL-01", "A05 NL1"]
Adjudication: load_scalar/read_interval use int() and therefore can truncate nonintegral JSON numbers or accept booleans. Strict separate preflight rejects demonstrated scalar cases; exact frozen input is well formed. No altered decoded false identity was accepted.
Disposition: Require one shared strict decoder at every entrypoint; preserve frozen v0.1 bytes.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3", "lines": [118, 119, 147, 148]}, {"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/RUN_RECEIPTS/author_checker_attack.stdout", "sha256": "17647c59ea9f4afc489a7f392b7ca0831f7525f2162ed053dc5448a57a4b5600"}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S02: Duplicate JSON keys use last-value semantics in mathematical entrypoints

Primary class: CONFIRMED_NONLOAD_BEARING_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A01", "A02", "A03", "A04", "A05"]; ["A01 G-04/N2", "A02 G-002", "A03 N2", "A04 NL-01", "A05 C07"]
Adjudication: Plain json.loads accepts duplicate scalar or top-level keys. Separate preflight unique_object rejects duplicates. This is malformed-input acceptance, not a false identity on frozen bytes.
Disposition: Use duplicate-key rejection for all mathematical JSON reads.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094", "lines": [10]}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/validate_integer_encoding.py", "sha256": "d4f9c72acbc54acbbedc21132848c52260cc2aaba0b3301f0237459bef4ffb6b", "lines": [16, 19, 24]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S03: Compact word float/Boolean aliases accepted by equality semantics

Primary class: CONFIRMED_NONLOAD_BEARING_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A04", "A05"]; ["A04 floating_integral_word_exponent", "A05 C04/C05"]
Adjudication: Integral float exponents and Boolean generator labels can equal the intended integers and pass core; named word preflight rejects them. No changed represented word escapes the mathematical test.
Disposition: Require actual integer word factors in all consumer paths.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3", "lines": [130, 134, 135, 194, 196, 199, 248, 282]}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/mutation_classifications.json", "sha256": "19cb9fa537c593b99e4d96375c356db03d17d3e47f677e3ed25aa1f749e34339", "lines": [75, 105, 139, 1055]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S04: Strict preflight misses Gram Q syntax

Primary class: CONFIRMED_NONLOAD_BEARING_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A05"]; ["A05 NL2/G10/G11"]
Adjudication: Q is stored as nested arrays rather than objects named word. Preflight therefore accepts Boolean/integral-float aliases even in a combined pipeline. Phase B combined Q=[true,1.0] passes both checks; [true,1.1] fails Gram, showing equality-preserving type aliases only.
Disposition: Add explicit required Q schema validation before mathematical comparison.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/validate_integer_encoding.py", "sha256": "d4f9c72acbc54acbbedc21132848c52260cc2aaba0b3301f0237459bef4ffb6b", "lines": [39, 50]}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3", "lines": [211, 212]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S05: Missing scalar members pass syntax-only preflight but fail mathematical consumer

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A04"]; ["A04 NL-02/missing_scalar_n/missing_scalar_d"]
Adjudication: Traversal recognizes scalar objects only if both n and d exist. Removing one means the preflight skips that malformed object; mathematical checker raises KeyError. Preflight explicitly claims syntax-only scope, so combined check fails closed.
Disposition: Document limited scope or upgrade to full required schema; do not portray preflight alone as certification.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/validate_integer_encoding.py", "sha256": "d4f9c72acbc54acbbedc21132848c52260cc2aaba0b3301f0237459bef4ffb6b", "lines": [4, 29, 59]}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/author_controls.json", "sha256": "f37378dd10421cdc281880ecaaf8db72deab75457fd64c830c5bb4402dbac864", "lines": [152, 958]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S06: Integer-string word schema mismatch is fail-closed

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A04", "A05"]; ["A04 integer_string_generator_interface", "A05 C26"]
Adjudication: Preflight permits integer strings in a word, while canon expects integer generator operations and rejects strings. This rejects an arguably permissible encoded input rather than accepting a false result.
Disposition: Choose and enforce one documented word-type schema.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/mutation_classifications.json", "sha256": "19cb9fa537c593b99e4d96375c356db03d17d3e47f677e3ed25aa1f749e34339", "lines": [75, 538, 547]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S07: Added explicit zero is mathematical no-op, storage count is not nonzero count

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A02", "A03", "A05"]; ["A02 G-004/NLB-02", "A03 G16/semantic boundary", "A05 C30"]
Adjudication: Appending a zero record at unused support keeps the SOS identical; core reports explicit_polynomial_coefficients=165. Frozen table actually has 164 nonzero coefficients. A02 calls this a defect, but acceptance is benign absent a canonical nonzero-support promise on arbitrary inputs; the output field itself does not say nonzero.
Disposition: Either prohibit explicit zeros as canonical schema or label counts stored/nonzero separately. Do not require a scientific repair.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094", "lines": [26, 31]}, {"path": "work/expanded/A02_5p6Sol_ExternalPrompt/outputs/FINAL_AUDIT_REPORT.md", "sha256": "c3407f09be8c98d3da3d4392a96b2c1cf6d5545228833e2ae213b5c5b8b17190", "lines": [11, 88, 130, 150, 152, 162, 252, 253, 259, 270, 272, 275, 278, 324]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S08: Theorem descriptors and proof bytes are not bound to checker PASS

Primary class: CONFIRMED_NONLOAD_BEARING_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A03", "A04", "A05"]; ["A03 wrong_descriptive_mu_polynomial", "A04 NL-03", "A05 NL3/C23/C24/C25/G09"]
Adjudication: All mathematical entrypoints check hard-coded mathematics, not PROOF.md or every descriptor. Coordinated Phase-B false-theorem/proof/polynomial/field mutations all pass preflight and mathematical entrypoints. This exposes interface-level statement binding, while the actual frozen statement is separately reconciled by scientific lanes. No proof of maximum 2 was obtained.
Disposition: Emit checker version, authoritative theorem identifier and verified input digests; explicitly separate annotations from enforced claims; bind frozen proof/document hashes in release wrapper.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_statement.py", "sha256": "b94e281b07a63224b95fa2ece2482f5ed774c99fa461d51a37f0a61c8ac76d37", "lines": [2, 17, 20, 26, 28, 29, 30, 31, 33, 40]}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "lines": [2, 3, 13, 14]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S09: Ignoring cached PASS flags, stored word universes and pivot enclosures is intentional

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["H03", "A04", "A05", "A07"]; ["H03 stored PASS flags ignored", "A04 legacy_*", "A05 G01/G08", "A07 NL-4"]
Adjudication: Reconstructing words, positivity and residuals rather than trusting diagnostic annotations is desirable. Flipping/erasing annotations must not be mistaken for a harmful mathematical mutation.
Disposition: Keep recomputation; explicitly mark ancillary/historical fields non-authoritative.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3", "lines": [8, 9, 213]}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/mutation_classifications.json", "sha256": "19cb9fa537c593b99e4d96375c356db03d17d3e47f677e3ed25aa1f749e34339", "lines": [551, 695]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S10: Duplicate diagnostic term IDs are benign to algebra but weak for provenance

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A04", "A05"]; ["A04 duplicate_term_ID_ignored", "A05 C09"]
Adjudication: The sum is indexed by list entries, not ID lookup. Duplicate IDs change diagnostics only and still pass mathematical checks. A stricter canonical certificate may prohibit them without changing theorem.
Disposition: Enforce unique IDs for traceability if adopting strict schema.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094", "lines": [12, 13]}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/mutations.json", "sha256": "1256444fa2c5981bb844db266b817af60b4e179c4aaa93e89e302241079c5a5d", "lines": [218]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S11: Valid rescaling, common phase, summand order and unreduced rationals remain valid

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A03", "A05"]; ["A03 G31", "A05 C27/C28/C31/C34"]
Adjudication: Consistent conjugation of both sides, R→2R with d→d/4, R→iR, summand permutation and unreduced rational encodings preserve represented mathematics. Acceptance is a positive control, not weakness.
Disposition: Retain benign-control regressions alongside corruption tests.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/benign_controls.json", "sha256": "5c60ff75749c0d7e711513c76e2653a53fa6fe3cc66db6a338e8e7d2464f93bc"}, {"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/mutations.json", "sha256": "ff8afa26d46a0663eb1fa80bb17566481278d8aebd95d10caf428b0b5ce0dc2f", "lines": [332]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S12: Rejection of equivalent noncanonical words is a format scope limit

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A05"]; ["A05 C29/C32/C33/G13"]
Adjudication: Splitting coefficients into duplicate records, cross-party raw word reversal and exponents 6 modulo 5 are algebraically equivalent but outside declared canonical input form. Rejection is not a theorem defect.
Disposition: Document canonical encoding and distinguish semantic corruption from canonical-format rejection.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/benign_controls.json", "sha256": "5c60ff75749c0d7e711513c76e2653a53fa6fe3cc66db6a338e8e7d2464f93bc"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S13: Dangling historical references in scientific payload

Primary class: CONFIRMED_NONLOAD_BEARING_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06 NLB-1/NLB-2"]
Adjudication: PROOF refers to NOVELTY_AND_SCOPE_AUDIT.md and EXACT_KERNELS declares field_relations_file exact_field.py, neither in reduced Phase-A payload. These are historical/provenance pointers; theorem is self-contained from displayed relations and serialized data.
Disposition: Mark references as historical/excluded and identify original-release paths; do not import missing code as proof premise.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "lines": [260]}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_KERNELS.json", "sha256": "6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5", "lines": [65113]}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/ATTACK_LEDGER.md", "sha256": "f79568eac7fee4e2d14d821d5f7474e2aab70d09b7f5372795f646c7e47cc8ef", "lines": [125, 126]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S14: Historical positivity-not-yet-certified status is not current evidence

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06 NLB-3"]
Adjudication: EXACT_SOS_CANDIDATE status records an earlier identity-only stage. Separate positivity certificate and actual recomputation establish positivity. Reading status in isolation is misleading but not inconsistent mathematics.
Disposition: Label status historical or remove stale annotation in a separately versioned package.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "lines": [2]}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/ATTACK_LEDGER.md", "sha256": "f79568eac7fee4e2d14d821d5f7474e2aab70d09b7f5372795f646c7e47cc8ef", "lines": [127]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "FIELD-006", "adjudication": "EXACT_IDENTITY_PASSED_POSITIVITY_NOT_YET_CERTIFIED records the candidate discovery stage; the separate final positivity certificate is rechecked. No checker trusts the status flags.", "evidence": [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "bytes": 132830}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json", "sha256": "22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de", "bytes": 182479}], "source_labels": ["A06:NLB-3", "A05:PB-D04"]}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S15: Nonconsecutive block labels do not contradict five blocks

Primary class: MISREPORT_OR_REJECTED_FINDING
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06 NLB-4"]
Adjudication: Labels [1,6,7,8,9] identify five blocks; no promise of consecutive numbering is violated. The observation is not a defect.
Disposition: Reject proposed scientific repair; optional explanatory label note only.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "lines": [13]}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/ATTACK_LEDGER.md", "sha256": "f79568eac7fee4e2d14d821d5f7474e2aab70d09b7f5372795f646c7e47cc8ef", "lines": [128]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "FIELD-005", "adjudication": "Labels 1,6,7,8,9 identify five blocks of sizes 2,4,3,3,2. Cardinality does not require consecutive IDs.", "evidence": [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "bytes": 132830}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json", "sha256": "22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de", "bytes": 182479}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}], "source_labels": ["A06:NLB-4"]}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S16: Correct k=0,1 convention is not a non-load-bearing defect

Primary class: MISREPORT_OR_REJECTED_FINDING
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06 NLB-5"]
Adjudication: Frozen standard five-outcome formula uses k=0,1. Comparing to a deliberately doubled 0..4 expression is a normalization control, not an error in frozen formula.
Disposition: Retain standard convention; route numerical coefficient comparison to convention lane.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/ATTACK_LEDGER.md", "sha256": "f79568eac7fee4e2d14d821d5f7474e2aab70d09b7f5372795f646c7e47cc8ef", "lines": [129]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "B-AT02", "adjudication": "Reject defect classification; k=0,1 is correct stated standard normalization. Summing reflected pairs through k=4 doubles the functional.", "evidence": [{"path": "outputs/RUN_RECEIPTS/attainment/exact_linkage.json", "sha256": "829b506d6b8685115cf2ce376857d2bf195c9e2231e097157720b0acd6afefeb"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}], "source_labels": ["A06:NLB-5", "A06:A-003"]}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S17: A07 no-silent-coercion claim is contradicted by inspected source

Primary class: MISREPORT_OR_REJECTED_FINDING
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 G-01"]
Adjudication: Claim that no silent coercion path was found cannot be used as evidence of strict parser coverage: author load_scalar plainly int-coerces, and A07 own parser also int-coerces. Phase-B replays reproduce accepted malformed encodings. A06 no-checker-defect report likewise must be narrowed to its actual checks.
Disposition: Correct coverage to frozen-data parse only; count strong malformed-input tests from A01–A05 rather than vote counts.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [40, 60, 79]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_exact_integer.py", "sha256": "0bd748964bce3df7254cc5a202bd1d7e90f220acf9a05d38a7fdd1e245668c6c", "lines": [189, 198]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/schema_attacks.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S18: A06 independent encoding audit is not strict

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06 G-002/R14"]
Adjudication: Extracted original encoding walk accepts denominator 1.5, Boolean generator, exponent1.9 and malformed integer string --3 with zero bad-scalar/word count. These are actual component executions. Frozen data remain clean; the alleged parser negative-control coverage was overstated.
Disposition: Replace int()/lstrip-is-digit validation with exact types/canonical strings, complete Q and fraction schemas, and executable malformed-input controls.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_operator_functional_bridge.py", "sha256": "888e2449ce9c0fd1cf9696fb9e14c613e40abf107de40178168fb7092047c45d", "lines": [44, 47, 53, 128]}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "49bcc3e101c9d961489df289583397a6dbb2058cf574568b9ecaf10678a7eabf", "lines": [299, 301]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/auditor_component_probes.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S19: A07 sign-flip controls actually triple a coordinate

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 G-02/M3/M6"]
Adjudication: bump(o,idx,2*n) yields n+2n=3n, not -n. Both selected coordinates are positive before and after. These tests detect coefficient changes but provide no sign-flip-specific evidence.
Disposition: Correct mutators to negate; Phase B freshly ran both true sign controls and both were rejected. Prior report must call historical tests coordinate tripling.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/g_mutation_controls.py", "sha256": "2554ebf40dc8d8e35e9d9e0ec23872fec8b0a7096a759e0f82889e29cb5aacee", "lines": [116, 121, 124]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/auditor_component_probes.json", "outputs/RUN_RECEIPTS/schema/corrected_negative_controls.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S20: A07 alternate-root control only changes target constant

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 M13/M-D"]
Adjudication: identity_residual(mu=alt) changes lhs constant but parse uses global MONO formed from MU_TRUE. Coefficients remain in original embedding. This is a valid wrong-bound test, not certificate reevaluation at another root.
Disposition: Relabel evidence and use actual full-field alternate embeddings from root lane for branch coverage.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/g_mutation_controls.py", "sha256": "2554ebf40dc8d8e35e9d9e0ec23872fec8b0a7096a759e0f82889e29cb5aacee", "lines": [21, 22, 24, 29, 48, 49, 122, 123, 139]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/I_exhaustion_receipt.txt", "sha256": "9fc10bab112068b7f5207f5e309c67b2d126870d5ddcb027a17479a2af88f434", "lines": [15, 50]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/auditor_component_probes.json"]
Supplementary deduplicated adjudications: [{"alias": "FIELD-008", "adjudication": "M13 changes target MU while precomputed MONO remains at MU_TRUE. It tests a constant target shift, not a field-conjugate certificate. i_exhaustion_gate.py also incorrectly calls a smaller root a weaker bound. The algebraic identity remains valid at compatible cubic roots; positivity fails there.", "evidence": [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md", "sha256": "81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119", "bytes": 2683}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/i_exhaustion_gate.py", "sha256": "705fd5ccd2a156c43a130286b9c2496faf04e4546fb32189e87ff0f0033fadd7", "bytes": 7420}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/g_mutation_controls.py", "sha256": "2554ebf40dc8d8e35e9d9e0ec23872fec8b0a7096a759e0f82889e29cb5aacee", "bytes": 7529}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/G_receipt.txt", "sha256": "815edf3d5a944b8410f3a153f024722a62b04e38ab5258c8cffc326d12dc149e", "bytes": 1951}], "source_labels": ["A07:N2", "A07:M-D", "A07:M13"]}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S21: A07 exact checker exits zero even for explicit FAIL

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 G_exact_on_M2", "PhaseB tiny coefficient mutation"]
Adjudication: Archived M2 gives 201 nonzero residuals and EXIT=0. Fresh Phase-B original-source M1 gives 37 nonzero residuals, verdict FAIL and exit0. An exit-code-only harness would misclassify both. Baseline exact zero residual is not invalidated.
Disposition: Return nonzero for failed mathematical status and require receipt status/residual, not exit alone.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_exact_integer.py", "sha256": "0bd748964bce3df7254cc5a202bd1d7e90f220acf9a05d38a7fdd1e245668c6c", "lines": [294, 295, 297, 299]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/G_exact_on_M2.txt", "sha256": "1950994769e142df655f7d3079547d4c58452b71732073c43a2d8116b0c724cd", "lines": [25, 45, 48]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/auditor_component_probes.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S22: A07 aggregate mutation summary does not reproduce final all-16 claim

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 G-02", "G_summary.json", "G_receipt.txt"]
Adjudication: Delivered g_mutation_controls executes13 named cases and retains three false values. M1/M2 numerical misses are expected precision limits; M2 exact replay is archived, M1 standalone exact receipt/mutant is absent but reproduced freshly in Phase B. Appended M11b results are not generated by delivered g source; benign widened box is correctly admissible. Final all16 summary cannot be obtained from one delivered driver.
Disposition: Preserve old misses, add consolidated reproducible exact/box runner and checked final summary with input/source hashes.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/G_summary.json", "sha256": "37bfae8a5c532d3330443fa66a2c8bcb256bfe7a826ec3073250cbfd58eba40c"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/G_receipt.txt", "sha256": "815edf3d5a944b8410f3a153f024722a62b04e38ab5258c8cffc326d12dc149e"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/g_mutation_controls.py", "sha256": "2554ebf40dc8d8e35e9d9e0ec23872fec8b0a7096a759e0f82889e29cb5aacee", "lines": [104, 115, 119, 136, 141, 143, 144, 145, 150]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/auditor_component_probes.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S23: A07 polynomial order and annotation-location prose are wrong

Primary class: MISREPORT_OR_REJECTED_FINDING
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 NL-4"]
Adjudication: SOS14.mu_polynomial [5,0,-65,0,144,96,16] is descending for stated sextic, not ascending. coefficient_zero_residual is a candidate annotation, not a positivity-certificate field. These are auditor report errors; core exact target is not changed.
Disposition: Correct report metadata descriptions; require field-name/location/order checks.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "4f6465c63d7886f8823047b031021f5584fe27d3836d0435269062f6b6fa7fe0", "lines": [205, 207]}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "lines": [3]}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "lines": [2754]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S24: A07 Gram redundancy argument overstates byte coverage

Primary class: MISREPORT_OR_REJECTED_FINDING
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 NL-3/N1/M-E"]
Adjudication: Compact SOS is sufficient for universal theorem independently of redundant Gram data. Matching81 basis words does not validate every E,H,L,D coefficient or prove compact–Gram equivalence. Other audits independently check that bridge.
Disposition: Mark A07 Gram/LDL as author replay/partial structural check, not independent exact Gram reconstruction; do not count redundant claims as extra independent votes.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "4f6465c63d7886f8823047b031021f5584fe27d3836d0435269062f6b6fa7fe0", "lines": [197, 200, 201]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/i_exhaustion_gate.py", "sha256": "705fd5ccd2a156c43a130286b9c2496faf04e4546fb32189e87ff0f0033fadd7", "lines": [23, 28, 42, 44, 119, 121]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-013", "adjudication": "N1 says compact anticommutator checking covers the same Gram parametrization, but only Q basis matching and supplied Gram checker replay are independent of its compact route. No independent E,H,L,D-to-R equality was checked by A07.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "4f6465c63d7886f8823047b031021f5584fe27d3836d0435269062f6b6fa7fe0"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S25: A07 failed partial diagnostics must not be counted as complete successful runs

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["C_receipt", "C_probe_receipt", "C_size_receipt", "B_receipt", "F_receipt"]
Adjudication: Earlier C receipt says FAIL; C_probe completes variant diagnostics but crashes on tuple-unpacking display; C_size stops at Python integer-to-string digit limit. Corrected exact C source/receipt supplies identity evidence; successful pre-error diagnostic values retain only their actually completed scope. Earlier B/F correction paths are distinct from final outputs.
Disposition: Retain partial records with terminal status, narrow coverage to completed steps, and provide final corrected driver receipts.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_receipt.txt", "sha256": "462f2128142e39998c9c7b0c19ed59369b0c4a45a931d5f98564f8ae9f72d7e0", "lines": [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_probe_receipt.txt", "sha256": "134d8939805992fd030f62a7878e2233897c2b75be263432282404b6d2f135ed", "lines": [4, 5, 6, 7, 34, 38]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_size_receipt.txt", "sha256": "120ed3ae5df0b47f85810baec2b4ca72420620785ae5c6dbcbb484e334316756", "lines": [9, 13]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-007", "adjudication": "Archived rational RHS loops only each monomial and adds coef at word*word-adjoint, omitting weights, coefficient products/conjugation and cross terms. Its own receipt is FAIL with one RHS word and 17 residuals. This is not a failed baseline certificate.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_independent.py", "sha256": "b02785106edda308ffaffe72116882a696278611dd72bf5e8922e89f7ed1259f"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_receipt.txt", "sha256": "462f2128142e39998c9c7b0c19ed59369b0c4a45a931d5f98564f8ae9f72d7e0"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/C_summary.json", "sha256": "87e364f4d846189e586f245debc8384cdcb9bef77526c964958c07a51234e228"}], "source_labels": []}, {"alias": "NC-008", "adjudication": "Four variant computations finish and distinguish coefficient conjugation and cross terms, but final display loop destructures a word as w,_ and crashes on the empty word. No completed end-to-end run or exact proof credit is justified.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_adjoint_convention_probe.py", "sha256": "015f742cf327a615e9b3ca0ee76b36230297c967de62a365fee497fcbaf38c3e"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_probe_receipt.txt", "sha256": "134d8939805992fd030f62a7878e2233897c2b75be263432282404b6d2f135ed"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S26: A03 and A04 initial mutation selectors aborted before intended checks

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A03", "A04"]; ["A03 attempt1 StopIteration", "A04 independent_controls.initial_failed"]
Adjudication: The selected dense coefficient had no zero slot. StopIteration is fixture construction failure, not rejection of a malformed certificate. Later corrected complete receipts supersede the failed runs; both failures preserved.
Disposition: Keep failures excluded from successful coverage and regression-test fixture selection.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/harness_revisions.md", "sha256": "43337842e050cc8509d66e4f920ba036b77f2e20b77e8f71a383dc808e6c7813"}, {"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/author_run_driver.attempt1.stderr.txt", "sha256": "077e24e89e1f209f002c5944335cc99dae86ceee0834acab554b5e77ca36e9f1"}, {"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/mutations.attempt1.stderr.txt", "sha256": "a806a45d556d12e18e925fb817c32cc75f97d3521058388edc209ecc11377be2"}, {"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/numerical_kill.attempt1.stderr.txt", "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/independent_controls.initial_failed.stdout.txt", "sha256": "02d3ff88ca822a2e423764ffa8dd0dc1fcb8723e5a4952bb2b53ef701ee2f52c"}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-015", "adjudication": "Both initially assume a dense first polynomial coefficient has a zero numerator. StopIteration prevents malformed-case execution. Later fixtures choose existing zero coordinates.", "evidence": [{"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/harness_revisions.md", "sha256": "43337842e050cc8509d66e4f920ba036b77f2e20b77e8f71a383dc808e6c7813"}, {"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/mutations.attempt1.stderr.txt", "sha256": "a806a45d556d12e18e925fb817c32cc75f97d3521058388edc209ecc11377be2"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/auditor_development_corrections.md", "sha256": "e64ca27d2b7f82ac3525d0fb10ae7d21fc313e1155c52d1889e7ba1fd65edc05"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/independent_controls.initial_failed.stdout.txt", "sha256": "02d3ff88ca822a2e423764ffa8dd0dc1fcb8723e5a4952bb2b53ef701ee2f52c"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S27: A04 argument-error rejection and partial sweeps are distinct from mathematical tests

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A04"]; ["A04 meta_exact.invalid_author_invocation", "A04 controls partial/author chunked runs"]
Adjudication: Initial new-support author invocation exited2 due to positional path instead of --root, not SOS residual. Corrected replay rejects with explicit residual.164-coefficient sweep uses sparse perturbation differences with14 full-term checks, not164 full executions. Chunked/resumed complete receipts replace timeouts.
Disposition: Preserve exact error categories and coverage granularity; validate stderr/status alongside return code.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/auditor_development_corrections.md", "sha256": "e64ca27d2b7f82ac3525d0fb10ae7d21fc313e1155c52d1889e7ba1fd65edc05"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.invalid_author_invocation.json", "sha256": "0e4f403a390e4291782622370fe912c4fc6029fb2f0260fd9adb711013cece5b", "lines": [6, 7]}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.json", "sha256": "e4498b12d2fddd9a31e632d07ee0ddfd71dd3e54d5642abe4726e9a5fe1c4870", "lines": [7]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-017", "adjudication": "Initial harness supplied positional JSON to --root verifier; nonzero exit did not establish mathematical rejection. Corrected invocation repeats run and reaches ArithmeticError residual rejection.", "evidence": [{"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/auditor_development_corrections.md", "sha256": "e64ca27d2b7f82ac3525d0fb10ae7d21fc313e1155c52d1889e7ba1fd65edc05"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.invalid_author_invocation.json", "sha256": "0e4f403a390e4291782622370fe912c4fc6029fb2f0260fd9adb711013cece5b"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.json", "sha256": "e4498b12d2fddd9a31e632d07ee0ddfd71dd3e54d5642abe4726e9a5fe1c4870"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S28: A05 development parser and arithmetic failures were corrected, not theorem failures

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A05"]; ["A05 independent_primitives.attempt1", "positivity development_run_1/2", "dead Fourier assertion", "N/N normalization"]
Adjudication: Original primitive parser wrongly rejected ancillary decimal metadata; positivity class initially lacked reverse subtraction; a supposedly invalid u enclosure was actually valid; a dead conjugation assertion and tautological N/N check required real cross-checks. Final sources/receipts document corrections and replay.
Disposition: Retain exact failure scope, corrected-source hashes and independent norm/Fourier tests; do not count aborted attempts as successful evidence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/verifier_branch/independent_primitives.attempt1.stderr.txt", "sha256": "84fb1f1a336c4a07702a552e978411e3cecec909fff2b03c7a1f0327cdc91955"}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_1.txt", "sha256": "b1276f7ee0dcd7e4b82f08f35fbab3076b6aa0f9b34a05b740b5451bbf6dc735"}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_2.txt", "sha256": "6fae0d8e1fab33141f085f758d54a61ec2e91b3ba6cde26181d9f63a1ab041bf"}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/FINAL_AUDIT_REPORT.md", "sha256": "3912a2d0f8cc020a14a48390911037655b9f483ee316ac08b2ee0c6c06caab2e", "lines": [82, 124]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "FIELD-011", "adjudication": "An alleged leakage mutation used [3.8,3.81], which genuinely encloses positive u. Final source uses leaking [3.8,3.803], while meta_audit.py retains [3.8,3.81] as a positive control.", "evidence": [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_2.txt", "sha256": "6fae0d8e1fab33141f085f758d54a61ec2e91b3ba6cde26181d9f63a1ab041bf", "bytes": 887}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/independent_positivity.py", "sha256": "d9bfc89945016be05c4753f9168b2801fc2ddc37145dc21323f9b31dda1bacb5", "bytes": 13100}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/meta_audit.py", "sha256": "0e676f89d0e98005eba88b9a5ba0c679896ed55929dba4e925f906c196249bbe", "bytes": 7536}], "source_labels": ["A05:positivity development_run_2", "A05:PB-G02"]}, {"alias": "FIELD-012", "adjudication": "Initial R class lacked __rsub__, causing TypeError before the embedding identities completed. Final source implements it and has clean receipts.", "evidence": [{"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_1.txt", "sha256": "b1276f7ee0dcd7e4b82f08f35fbab3076b6aa0f9b34a05b740b5451bbf6dc735", "bytes": 624}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/independent_positivity.py", "sha256": "d9bfc89945016be05c4753f9168b2801fc2ddc37145dc21323f9b31dda1bacb5", "bytes": 13100}], "source_labels": ["A05:positivity development_run_1"]}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S29: A01 numerical checker can falsely emit PASS with assertions disabled

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A01"]; ["PhaseB -O attack"]
Adjudication: On weight+1 corruption, original A01 concrete checker rejects normally but -O removes final asserts and emits PASS despite residuals>1. Frozen author checker still rejects under -O. The A01 exact core uses explicit need checks, so this finding is limited to numerical corroboration/runtime flag semantics.
Disposition: Add optimize guard or explicit failure checks, record optimize flag, and require results to satisfy declared numerical thresholds.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/INDEPENDENT_CHECKS/concrete_representation_sos_check.py", "sha256": "b0b38b62525a6822d8fb02c2e5fb94ddaa84651dc5f6cc80fed345569227a5d0", "lines": [64, 65]}]
Independent reproduction: ["outputs/RUN_RECEIPTS/schema/optimization_mode_attack.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S30: Author entrypoints and several audit paths are correlated evidence families

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01", "A02", "A03", "A04", "A05", "A06", "A07", "H01", "H02", "H03"]; ["A07 M-A/NL-1", "A06 M1/M3", "all independence caveats"]
Adjudication: verify_sos14 and verify_statement import verify_independent arithmetic/normalizer/interval logic; H03 is author-side mutation of same engine. Each auditor mostly shares one scalar/parser/reducer within its exact suite. Different models/prompts do not imply independent target semantics. H01 second tower checker and alternate modular/direct-matrix paths add genuinely distinct implementation dimensions with explicit limits.
Disposition: Use per-node ancestry matrix, not majority PASS. Compact/Gram identical weights are one positivity object, not two independent proofs.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094", "lines": [7]}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_statement.py", "sha256": "b94e281b07a63224b95fa2ece2482f5ed774c99fa461d51a37f0a61c8ac76d37", "lines": [8]}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "49bcc3e101c9d961489df289583397a6dbb2058cf574568b9ecaf10678a7eabf", "lines": [112, 200, 283, 286, 287, 345, 393]}, {"path": "work/expanded/H01_Web6Pro_independent_audit/CGLMP5_independent_audit/crosscheck.py", "sha256": "98600f8a694821ad10c728bb7f906150bf294688562b57c1ef11f5074a32d22b", "lines": [4, 7]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "FIELD-013", "adjudication": "verify_sos14 imports verify_independent arithmetic, reducer, positivity and physical checks. This is one underlying author engine, though two certificate data paths. PROOF §7 already explicitly discloses the reuse.", "evidence": [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094", "bytes": 2230}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3", "bytes": 15908}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}], "source_labels": ["A07:NL-1/M-A"]}, {"alias": "NC-001", "adjudication": "verify_sos14 imports ZERO,MU,load_scalar,canon,star,word_product,make_bell,interval_basis,positive and physical checking from verify_independent. Historical kill_tests imports the same engine. These executions are not independent arithmetic/normal-form votes. PROOF explicitly discloses compact arithmetic reuse.", "evidence": [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S31: Hashes establish supplied byte identity, not external provenance or audit blindness

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01", "A02", "A03", "A04", "A05", "A06", "A07", "H01", "H02"]; ["source release identity", "historical exposure", "novelty limits"]
Adjudication: All outer corpus hashes and current manifests identify supplied bytes. They do not independently authenticate commit history, publication time, authorship, actual model isolation or unavailable historical input. H02 explicitly discloses prior AI notes and incomplete generation history; no external project lookup was performed in Phase B.
Disposition: Keep provenance claims bounded; no theorem premise may rely on unseen history or novelty status.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/FROZEN_SOURCE_REFERENCE.md", "sha256": "367d2c70cf296027826ff50f1cc621cea56ba978c028c42eb4f26f0ec7312a6d"}, {"path": "work/corpus/CGLMP5_PHASE_B_FINAL/historical_pre_phase_a/H02_INTERNAL_POST_ONESHOT_VERIFICATION_RECORD.md", "sha256": "e84dbd033d581fea965c2fb016218f8e6e9eb75ad7e6cc3ea64830f6a6672b02", "lines": [3, 7, 11, 17, 24, 30, 32, 37, 40, 44, 48, 50, 61, 62, 68, 76, 78, 86, 105, 107]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S32: Historical nested manifest mismatch is disclosed path normalization

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["H02"]; ["BASE-RELEASE lower_worker/SHA256SUMS.txt"]
Adjudication: Two nested historical checksums differ from curated report/environment text; packaging_identity maps source hashes to current hashes and current outer MANIFEST validates all bytes. A05 branch manifests likewise use archive-root relative paths and all123 entries verify from declared root; initial wrong-base checks are not corruption.
Disposition: Label historical manifests and required cwd; retain original→curated mapping. Do not rewrite historical hashes as if original receipts were unchanged.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_v0.1_C001/CGLMP5_v0.1/verification/receipts/packaging_identity.json", "sha256": "b603d7e0649e2907e9c01b3e75e54e3bc2e681e2d8332880c16009ccd40740ea"}, {"path": "work/expanded/CGLMP5_v0.1_C001/CGLMP5_v0.1/verification/receipts/reconstruction/lower_worker/SHA256SUMS.txt", "sha256": "5035433d028803c11b9da876853f1238b0753a116c2fac857c63191f3b8e2b7a"}]
Independent reproduction: ["outputs/lanes/schema/manifest_checks_resolved.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S33: A06/A07 reproduction requires path staging or explicit path adaptation

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A06", "A07"]; ["A06 README run instructions", "A07 hardcoded PAY paths"]
Adjudication: A06 audit ZIP omits sibling PHASE_A_BLIND_AUDIT expected by source. A07 many scripts hardcode a historical Windows PAY path. Mathematical tests can be replayed by staging frozen bytes or adding configurable paths; as-delivered launch instructions are not generally relocatable.
Disposition: Add explicit --root/--output and documented dependency versions; preserve input/source hashes and record any adapter separately.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/RUN_INSTRUCTIONS.md", "sha256": "613cf6e1855411dc0cef3ce4bd36d08ed55c738a1aa60657c01394ef20d7d30c", "lines": [7, 8, 19]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/g_mutation_controls.py", "sha256": "2554ebf40dc8d8e35e9d9e0ec23872fec8b0a7096a759e0f82889e29cb5aacee", "lines": [18]}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/README.md", "sha256": "328b4d85e1da6486add3fce95671fe72766a12372453c99557c2526c732f0db2", "lines": [17, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 43]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S34: A01 source-exposure timing limits blind-plan independence

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01"]; ["A01 meta-audit source-code exposure before formal plan"]
Adjudication: A01 explicitly acknowledges source-code exposure before formal attack plan; the preserved plan claims only before executing author checkers. This does not erase independent implementation but prevents stronger claim that all source was unseen before planning.
Disposition: Describe actual exposure boundary and retain plan timestamp caveat; do not infer system-level/model independence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "01a874b1cc6b957d09ad42e1db942fa49faccb4fd1a821b79fe7e9e268d1eed2", "lines": [243]}, {"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/INDEPENDENT_CHECKS/ATTACK_PLAN_PRECHECK.md", "sha256": "6043c157ca87ce9aac0005bd75169129368b34f1019109e7d3725abecfb88225", "lines": [1]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-002", "adjudication": "A01 META-01 admits reading supplied checker source before the formal pre-check plan. It still writes a distinct Groebner table and direct-event strategy implementation.", "evidence": [{"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "01a874b1cc6b957d09ad42e1db942fa49faccb4fd1a821b79fe7e9e268d1eed2"}, {"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "497cc0d8eb32b2e985251800617d4aaecaecaa0206d5497e2b1afe8045011bb1"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD01: D-shift omitted in initial physical encoding

Primary class: DUPLICATE_OF_B-AT04
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug1"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [86]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD02: Cross-party commutation tested on bare local matrices

Primary class: DUPLICATE_OF_B-AT04
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug2"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [87]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD03: Factor-five error in root numeric diagnostic

Primary class: DUPLICATE_OF_FIELD-009
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug3"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [89]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD04: Unreduced z powers and unscaled cubic terms in initial field code

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug4"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [90]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-009", "adjudication": "Reported earlier unreduced z^18/z^19 and unscaled cubic additions were field-engine defects. Final archived routines visibly perform proper reduction/scaling, but those old source versions are not all preserved.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_independent.py", "sha256": "b02785106edda308ffaffe72116882a696278611dd72bf5e8922e89f7ed1259f"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD05: Missing cross terms/conjugation/word normalization in early SOS

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug5"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [92]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD06: Wrong x-squared basis and omega phase in early exact SOS

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug6"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [22, 94]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-010", "adjudication": "Comments and ledger describe b=2 parsed as x instead of x^2 and omega^(-k) encoded as zeta^(-k) instead of zeta^(-4k). Final code uses repeated x multiplication and phase -4k; fresh integer replay has zero residual on 273 words.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_exact_integer.py", "sha256": "0bd748964bce3df7254cc5a202bd1d7e90f220acf9a05d38a7fdd1e245668c6c"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_exact_receipt.txt", "sha256": "2f588309f6dcd27fb4ac09d7c4de533df6cd95209323537331506b3a62246f68"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD07: Naive V E V-adjoint used as projector

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug7"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [97]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD08: Hadamard instead of matrix product and wrong commutator metric

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug8"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [99]}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-011", "adjudication": "Archived source documents earlier Hadamard product instead of matrix multiplication and comparison of operators instead of commutator. Final source uses q@diag and tensor commutator, with assertions.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/cd_noncommutative_and_positivity.py", "sha256": "0bb0751455ff82bac9d4dd41159b1e364ec2887485b106f8f42d4c4ee58fadef"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}], "source_labels": []}]
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD09: Initial mutation detector ignored boxes and omitted M10

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug9"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [101]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-SD10: Floating evaluation of exact root endpoints created false alarm

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07 bug10"]
Adjudication: Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.
Disposition: Retain historical bug log; use final successful artifact and independent lane checks; do not count development failures as theorem refutations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [103]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-S35: A06 corrected D-shift and tensor-factor errors are auditor history

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06 meta-audit8.5/A-004/F-005"]
Adjudication: Report discloses initial omitted D shifts and tensor-factor ordering mistake. Earlier failing source/run artifacts are not separately preserved in A06. Final sources/receipts support corrected checks, not reconstructed history of every failed attempt.
Disposition: Record disclosure and missing intermediate receipts without treating absent history as invalid frozen theorem.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "49bcc3e101c9d961489df289583397a6dbb2058cf574568b9ecaf10678a7eabf", "lines": [319, 320, 322]}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/schema/findings.json (SHA-256 e91253f2bc2a34ae5254297b0284052787b7224e6969196780114eb22ad17b89)

## B-E01: A07 E-01b uses setting-dependent states instead of one common embedded state

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07 E-01b", "A07 e_povm_bridge.py joint-probability section", "A07 final report common-space numerical claim"]; ["A07 E-01b", "A07 e_povm_bridge.py joint-probability section", "A07 final report common-space numerical claim"]
Adjudication: A07 E-01b uses setting-dependent states instead of one common embedded state
Disposition: Withdraw numerical common-state claim; baseline analytic construction remains valid
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "RUN_RECEIPTS/bridge/a07_fixed_embedding_attack.json", "sha256": "cb7a33739975ad87c65dbaf3a13687808e2b0eb706197911c704ea77eef42ef2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/bridge/findings.json (SHA-256 a88b192168fcf8f917e5a5655479be76c79573316ec2a144f9d639b26eadd187)

## B-E02: A07 rank-one POVM generator has rank at most5 and does not normalize at d6

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07 E-01a d6"]; ["A07 E-01a d6"]
Adjudication: A07 rank-one POVM generator has rank at most5 and does not normalize at d6
Disposition: Exclude invalid d6 instance; valid dimensions still refute naive direct-effect encoding
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "RUN_RECEIPTS/bridge/a07_fixed_embedding_attack.json", "sha256": "cb7a33739975ad87c65dbaf3a13687808e2b0eb706197911c704ea77eef42ef2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/bridge/findings.json (SHA-256 a88b192168fcf8f917e5a5655479be76c79573316ec2a144f9d639b26eadd187)

## B-E03: Direct Fourier sum of general POVM effects need not be unitary; dilation is essential and present

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A07 E-01a", "A07 rejected V E V* projector attempt", "A01/A02/A03/A04/A05/A06 universal bridge reasoning"]; ["A07 E-01a", "A07 rejected V E V* projector attempt", "A01/A02/A03/A04/A05/A06 universal bridge reasoning"]
Adjudication: Direct Fourier sum of general POVM effects need not be unitary; dilation is essential and present
Disposition: Treat as a negative control, not a baseline defect
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "lanes/bridge/ANALYTIC_UNIVERSAL_BRIDGE.md", "sha256": "ee155d02fa03b8a006df63abe49ee512c8f79b58c1572c46cfef8664e538f7f5"}, {"path": "RUN_RECEIPTS/bridge/exact_common_space.json", "sha256": "2244bd5314ed9e840e148e0e9739616e86bfd0f607618f56c5754c3f48764409"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/bridge/findings.json (SHA-256 a88b192168fcf8f917e5a5655479be76c79573316ec2a144f9d639b26eadd187)

## B-E04: Frozen §5 terse common-space proof is valid, including infinite/nonseparable local spaces, mixed/nonnormal states; no abstract commuting-POVM scope is added

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A07 NL-2", "A01 universal bridge", "A02 universal receipt", "A03 E01/E02", "A04 E-01/E-02", "A05 E1", "A06 E-001/E-002/E-003/E-004/E-006", "H01 §6", "H02 common-embedding rejected objection"]; ["A07 NL-2", "A01 universal bridge", "A02 universal receipt", "A03 E01/E02", "A04 E-01/E-02", "A05 E1", "A06 E-001/E-002/E-003/E-004/E-006", "H01 §6", "H02 common-embedding rejected objection"]
Adjudication: Frozen §5 terse common-space proof is valid, including infinite/nonseparable local spaces, mixed/nonnormal states; no abstract commuting-POVM scope is added
Disposition: Optional expanded explanation of the fixed common embedding and defect-projection alternative; no repair required
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "lanes/bridge/ANALYTIC_UNIVERSAL_BRIDGE.md", "sha256": "ee155d02fa03b8a006df63abe49ee512c8f79b58c1572c46cfef8664e538f7f5"}, {"path": "RUN_RECEIPTS/bridge/formal_isometry_bridge.json", "sha256": "3f6d617a247c5a4d238e31d648e59cdcfb402d53fce38968ec73dcff1b5763df"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/bridge/findings.json (SHA-256 a88b192168fcf8f917e5a5655479be76c79573316ec2a144f9d639b26eadd187)

## B-E05: Compression is positive but not multiplicative; do not substitute POVM effects directly into same-party SOS products

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["New Phase B cross-audit interpretation attack"]; ["New Phase B cross-audit interpretation attack"]
Adjudication: Compression is positive but not multiplicative; do not substitute POVM effects directly into same-party SOS products
Disposition: Rejected shortcut is not used in baseline; preserve full dilated identity then take state expectation
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "RUN_RECEIPTS/bridge/compression_product_attack.json", "sha256": "e4f60d2fc2859df42da33444a45648e809e2372b254039bb3562ecb2e20cd6b3"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/bridge/findings.json (SHA-256 a88b192168fcf8f917e5a5655479be76c79573316ec2a144f9d639b26eadd187)

## B-E06: Numerical common-space tests at9d and11d use different valid complement spaces; dimension discrepancy is not mathematical disagreement

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01/A02/A03/A05/A06 9d construction", "A04 6d Halmos and11d reused-Halmos direct sum"]; ["A01/A02/A03/A05/A06 9d construction", "A04 6d Halmos and11d reused-Halmos direct sum"]
Adjudication: Numerical common-space tests at9d and11d use different valid complement spaces; dimension discrepancy is not mathematical disagreement
Disposition: Record shared analytic premise and nonindependence of A04 two implementations at square-root/Halmos layer
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "lanes/bridge/ANALYTIC_UNIVERSAL_BRIDGE.md", "sha256": "ee155d02fa03b8a006df63abe49ee512c8f79b58c1572c46cfef8664e538f7f5"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/bridge/findings.json (SHA-256 a88b192168fcf8f917e5a5655479be76c79573316ec2a144f9d639b26eadd187)

## FIELD-001: Largest root and positive real algebraic embedding are valid

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01", "A02", "A03", "A04", "A05", "A06", "A07", "H01", "H02"]; ["A02:B-001/B-002/B-003", "A03:B01/B02", "A05:PB-B01/PB-B02", "A06:B-001..B-006", "A07:B-01..B-08", "H01:§3", "H02:root/embedding attack"]
Adjudication: p has six real roots; exactly one above 3 and none above 31/10. s=A(mu)/B(mu)>0 at that root; positive u and the sector select zeta=exp(i*pi/10). Fresh Bezout certificate proves B is nonzero at all roots. Twelve real (mu,u-sign) embeddings were examined, with s sign determined by A/B.
Disposition: Retain theorem and root wording. Add portable exact sign witness to regression evidence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md", "sha256": "81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119", "bytes": 2683}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}]
Independent reproduction: ["RUN_RECEIPTS/field/sturm_tarski_weights.json", "RUN_RECEIPTS/field/fraction_sign_meta.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-002: Irreducibility is not required for these exact-zero certificates

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01", "A02", "A03", "A04", "A05", "H01", "H02"]; ["A05:dependency analysis", "H01:§3", "H02:§3"]
Adjudication: Every reduction relation holds at the stated actual numbers. Evaluation is a homomorphism, so formal zero implies actual zero even without proving the quotient a field. Main verifier uses only rational divisions. The new B inverse is explicitly checked, so elimination also has no unverified inversion.
Disposition: Reject requests to add irreducibility as a missing load-bearing theorem assumption; optional expository clarification only.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md", "sha256": "81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119", "bytes": 2683}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3", "bytes": 15908}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "NC-018", "adjudication": "All exact engines use the printed actual-number relations. A zero produced solely by sound polynomial identities evaluates to zero in the actual embedding whether or not the quotient basis is minimal/faithful. Branch and positivity remain separate obligations.", "evidence": [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/sos_branch/SOS_BRANCH_REPORT.md", "sha256": "17f0279f294684a46784be8b9abdbc57dda4df8ac0ee94b11396f16093e3f91e"}], "source_labels": []}]
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-003: Strict reality and positivity of all fourteen weights survives a non-box oracle

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01", "A02", "A03", "A04", "A05", "A06", "H01", "H02", "H03"]; ["A01:positivity", "A02:D-001/D-002/D-005", "A03:D01", "A05:PB-D01", "A06:D", "H01:§5", "H03:negative H/LDL sign"]
Adjudication: All imaginary coordinates are exactly zero. Fresh univariate elimination plus Sturm–Tarski determines signs without frozen embedding boxes or prior interval code. All weights and matching D pivots exceed 1/3000; minimum is id 9:1, strictly between 3584887/10^10 and 3584888/10^10. Fraction-only reimplementation independently agrees on 210 sign comparisons.
Disposition: Retain strict positivity claim. Cite exact sign or rational bounds, never numerical spectra as proof.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json", "sha256": "22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de", "bytes": 182479}]
Independent reproduction: ["RUN_RECEIPTS/field/sturm_tarski_weights.json", "RUN_RECEIPTS/field/fraction_sign_meta.json", "RUN_RECEIPTS/field/a05_bernstein_replay/positivity_bernstein_meta_results.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-004: Gram and compact weights coincide, so repeated pivots are not independent sign votes

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01", "A02", "A03", "A04", "A05", "A06", "A07", "H01", "H02"]; ["A02:D-003/D-004", "A03:D02/C02", "A05:PB-D02/PB-D03", "A06:M3", "A07:D-02/NL-3/N1", "H01:§5"]
Adjudication: All fourteen D values are the compact weights. H=LDL* and conjugated EL columns are an additional serialized data-path consistency check, not new positivity facts. Five small H blocks are positive definite, whereas arbitrary 81-row E embeddings yield a positive-semidefinite total Gram.
Disposition: Keep Gram as auxiliary structural/regression coverage. Do not count its fourteen pivots as independent positivity evidence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json", "sha256": "22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de", "bytes": 182479}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "bytes": 132830}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_KERNELS.json", "sha256": "6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5", "bytes": 935169}]
Independent reproduction: ["RUN_RECEIPTS/field/gram_elimination.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-005: Nonconsecutive block labels are benign

Primary class: DUPLICATE_OF_B-S15
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06:NLB-4"]
Adjudication: Labels 1,6,7,8,9 identify five blocks of sizes 2,4,3,3,2. Cardinality does not require consecutive IDs.
Disposition: Reject the proposed defect classification; no scientific or schema change needed.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "bytes": 132830}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json", "sha256": "22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de", "bytes": 182479}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-006: Historical candidate status is a stage marker

Primary class: DUPLICATE_OF_B-S14
Frozen theorem changes: False
Auditors/source labels: ["A06", "A05"]; ["A06:NLB-3", "A05:PB-D04"]
Adjudication: EXACT_IDENTITY_PASSED_POSITIVITY_NOT_YET_CERTIFIED records the candidate discovery stage; the separate final positivity certificate is rechecked. No checker trusts the status flags.
Disposition: Optional documentation: label the field as discovery-stage status. Do not edit the frozen scientific theorem or misclassify as invalid positivity.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/EXACT_SOS_CANDIDATE.json", "sha256": "14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649", "bytes": 132830}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json", "sha256": "22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de", "bytes": 182479}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-007: A07 numerical positivity cannot support a rigorous independent sign verdict

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07:D-01", "A07:FINAL §3.3/§8"]
Adjudication: cd_noncommutative_and_positivity.py uses mpmath 50 dps but starts XN from binary float MU; it evaluates signs numerically and converts to complex. It contains no rigorous interval sign engine. Its claim that positivity was numerically certified and supported by finite representation PSD is too strong. Fraction was available in its own harness, so this was not a demonstrated hard stop. Author replay supplies rigorous positivity but is correlated evidence.
Disposition: Downgrade A07 D-01 to numerical diagnostic; retain author replay separately. Correct audit completeness/independence language. Central gap closed by other exact evidence and fresh Phase B sign oracle.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/POSITIVITY_CERTIFICATE.json", "sha256": "22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de", "bytes": 182479}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/cd_noncommutative_and_positivity.py", "sha256": "0bb0751455ff82bac9d4dd41159b1e364ec2887485b106f8f42d4c4ee58fadef", "bytes": 7241}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/CD_receipt.txt", "sha256": "456e5cd4779abf2ec33e57d1b123b3658e94ae0de8acc60c82aaaf1783c7597f", "bytes": 1123}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "4f6465c63d7886f8823047b031021f5584fe27d3836d0435269062f6b6fa7fe0", "bytes": 23026}]
Independent reproduction: ["RUN_RECEIPTS/field/sturm_tarski_weights.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-008: A07 root mutation did not re-evaluate the coefficient embedding

Primary class: DUPLICATE_OF_B-S20
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07:N2", "A07:M-D", "A07:M13"]
Adjudication: M13 changes target MU while precomputed MONO remains at MU_TRUE. It tests a constant target shift, not a field-conjugate certificate. i_exhaustion_gate.py also incorrectly calls a smaller root a weaker bound. The algebraic identity remains valid at compatible cubic roots; positivity fails there.
Disposition: Correct N2/M-D/M13 coverage and stronger/weaker wording. Replace with the exact twelve-branch census; only the three s-positive roots represent alternative mu with fixed s=+sqrt5.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md", "sha256": "81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119", "bytes": 2683}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/i_exhaustion_gate.py", "sha256": "705fd5ccd2a156c43a130286b9c2496faf04e4546fb32189e87ff0f0033fadd7", "bytes": 7420}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/g_mutation_controls.py", "sha256": "2554ebf40dc8d8e35e9d9e0ec23872fec8b0a7096a759e0f82889e29cb5aacee", "bytes": 7529}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/G_receipt.txt", "sha256": "815edf3d5a944b8410f3a153f024722a62b04e38ab5258c8cffc326d12dc149e", "bytes": 1951}]
Independent reproduction: ["RUN_RECEIPTS/field/sturm_tarski_weights.json", "RUN_RECEIPTS/field/fraction_sign_meta.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-009: A07 first root script omitted a factor five in A squared

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07:I-02 bug 3", "A07:B-01/B-04 correction"]
Adjudication: The original numeric/remainder probe used 5*(t^3-4t-4)^2 rather than 25*(...)^2 and produced spurious residuals. Its earlier symbolic A^2-5B^2 line was correct. The correction source and receipt repair the test.
Disposition: Preserve both failed/corrected artifacts; do not attribute the false alarm to the theorem.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md", "sha256": "81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119", "bytes": 2683}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/b_root_embedding.py", "sha256": "77267f5eb696b963cb545597ca02ad6aae4c100b2988a061ea89b08cab6db534", "bytes": 6775}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/b_root_embedding_correction.py", "sha256": "1848718c2c45c5b6930d6ee9c5e5c72167b8e2f1b1ff9a2c24d43498611327a6", "bytes": 3015}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/B_receipt.txt", "sha256": "b1a4666efb304aee6a96b43d8944b18beef377a521d19a2e76168fb44a55f1f8", "bytes": 3115}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/B_receipt_correction.txt", "sha256": "911af6085f9e841d7c02a44a48143050eb626305cad84337242a43db8d5e870b", "bytes": 1304}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "B-SD03", "adjudication": "Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [89]}], "source_labels": ["A07 bug3"]}]
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-010: A07 treated a displayed decimal prefix as a 50-digit equality

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; ["A07:B-02 correction"]
Adjudication: The printed mu ends before the exact root decimal, so a 10^-50 comparison against the prefix fails by approximately 2.95e-49. The correction correctly recognizes truncation.
Disposition: Preserve correction; no change to ellipsis-marked theorem decimal needed.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/b_root_embedding_correction.py", "sha256": "1848718c2c45c5b6930d6ee9c5e5c72167b8e2f1b1ff9a2c24d43498611327a6", "bytes": 3015}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/B_receipt_correction.txt", "sha256": "911af6085f9e841d7c02a44a48143050eb626305cad84337242a43db8d5e870b", "bytes": 1304}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-011: A05 initially expected rejection of a valid coarse u enclosure

Primary class: DUPLICATE_OF_B-S28
Frozen theorem changes: False
Auditors/source labels: ["A05"]; ["A05:positivity development_run_2", "A05:PB-G02"]
Adjudication: An alleged leakage mutation used [3.8,3.81], which genuinely encloses positive u. Final source uses leaking [3.8,3.803], while meta_audit.py retains [3.8,3.81] as a positive control.
Disposition: Keep corrected negative and positive controls; classify original failed assertion as harness defect, not checker escape.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_2.txt", "sha256": "6fae0d8e1fab33141f085f758d54a61ec2e91b3ba6cde26181d9f63a1ab041bf", "bytes": 887}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/independent_positivity.py", "sha256": "d9bfc89945016be05c4753f9168b2801fc2ddc37145dc21323f9b31dda1bacb5", "bytes": 13100}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/meta_audit.py", "sha256": "0e676f89d0e98005eba88b9a5ba0c679896ed55929dba4e925f906c196249bbe", "bytes": 7536}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-012: A05 positivity development had missing reverse subtraction

Primary class: DUPLICATE_OF_B-S28
Frozen theorem changes: False
Auditors/source labels: ["A05"]; ["A05:positivity development_run_1"]
Adjudication: Initial R class lacked __rsub__, causing TypeError before the embedding identities completed. Final source implements it and has clean receipts.
Disposition: Keep failure provenance; no mathematical consequence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/positivity_branch/development_run_1.txt", "sha256": "b1276f7ee0dcd7e4b82f08f35fbab3076b6aa0f9b34a05b740b5451bbf6dc735", "bytes": 624}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/positivity_branch/independent_positivity.py", "sha256": "d9bfc89945016be05c4753f9168b2801fc2ddc37145dc21323f9b31dda1bacb5", "bytes": 13100}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-013: A07 independence caveat about supplied checkers is valid and already disclosed

Primary class: DUPLICATE_OF_B-S30
Frozen theorem changes: False
Auditors/source labels: ["A07", "H02"]; ["A07:NL-1/M-A"]
Adjudication: verify_sos14 imports verify_independent arithmetic, reducer, positivity and physical checks. This is one underlying author engine, though two certificate data paths. PROOF §7 already explicitly discloses the reuse.
Disposition: Count as correlated replay; no new theorem defect or undisclosed independence claim.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094", "bytes": 2230}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3", "bytes": 15908}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-014: A06 other-root positivity sensitivity was numerical, not exact

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06:N3", "A06:R15"]
Adjudication: chk_root_sensitivity.py uses 50-digit mpmath on the three roots with fixed positive sqrt5. Counts 6 and 5 negative weights at the two smaller compatible roots agree with fresh exact signs; it did not certify root sign comparisons.
Disposition: Keep as noncertifying diagnostic; Phase B exact branch census upgrades the scientific coverage.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_root_sensitivity.py", "sha256": "519c5d13a47327a204c9baac1dd7cc22c78a303915867eeca9bac060eb1d074a", "bytes": 2769}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R15_root_sensitivity.txt", "sha256": "48c13978cd31774a0d39e87fb6296d0c700a59a7bb2598f66dc82f7a3747b9e5", "bytes": 889}]
Independent reproduction: ["RUN_RECEIPTS/field/sturm_tarski_weights.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-015: A06 Gaussian algebraic inversions verify units explicitly

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; ["A06:B-006", "A06:cglib F.inv"]
Adjudication: The report sometimes uses formal nonzero tests, which alone need not establish nonzero actual values in an arbitrary quotient. But F.inv solves the multiplication system and checks self*out==ONE; actual evaluation therefore proves every inverted element nonzero without irreducibility.
Disposition: Do not manufacture a division gap. Explain the explicit unit-identity check when describing A06 arithmetic.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md", "sha256": "81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119", "bytes": 2683}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/cglib_audit.py", "sha256": "f5736db1e42d4ed4bd5f843d4ccf29e089296b63640adedd277ba7a5b0ee6822", "bytes": 8650}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-016: Phase-B sign crosscheck first attempt compared different zero polynomial serializations

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["PHASE_B"]; ["FIELD-META-ATTEMPT1"]
Adjudication: Fraction tuple () represents zero while SymPy all_coeffs() uses [0]. A serialization equality assertion aborted before the meta-check verdict. No sign result was accepted; correction normalizes both representations and the full rerun passes 210 checks.
Disposition: Preserve attempt1 source and stderr; include in run provenance.
Limitations: See scoped evidence
Frozen bytes / raw evidence: []
Independent reproduction: ["RUN_RECEIPTS/field/fraction_sign_meta.attempt1.stderr", "RUN_RECEIPTS/field/fraction_sign_meta.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## FIELD-017: Fresh attainment quotient is tied to the physical real embedding and nonzero state

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["PHASE_B"]; ["ATTAINMENT:exact_linkage"]
Adjudication: Independent cross-map verifies all 576 quartic-u/cubic-mu basis products, 24 conjugations and 24 serialized basis maps. Exact actual-root signs give d>4, five positive cleared state components and positive norm; phase identities and sector fix zeta.
Disposition: Cite the field crossreview alongside attainment exact_linkage. Rerun if reviewed source hash changes.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2", "bytes": 581335}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/ROOT_EMBEDDING.md", "sha256": "81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119", "bytes": 2683}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee", "bytes": 13360}]
Independent reproduction: ["RUN_RECEIPTS/field/attainment_field_crossreview.json"]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/field/findings.json (SHA-256 ab45ff91ba0d89aff3f1a907d67a8d57261fc4665ef9a3404c0cbf59a4e01518)

## NC-001: Author checkers share one arithmetic and normalizer implementation

Primary class: DUPLICATE_OF_B-S30
Frozen theorem changes: False
Auditors/source labels: ["BASE", "H03", "A07"]; []
Adjudication: verify_sos14 imports ZERO,MU,load_scalar,canon,star,word_product,make_bell,interval_basis,positive and physical checking from verify_independent. Historical kill_tests imports the same engine. These executions are not independent arithmetic/normal-form votes. PROOF explicitly discloses compact arithmetic reuse.
Disposition: Collapse supplied verifier and historical kill-test evidence into shared implementation ancestry; retain actual tests, no scientific change.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_sos14.py", "sha256": "90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-002: A01 pre-plan source exposure limits procedural blindness

Primary class: DUPLICATE_OF_B-S34
Frozen theorem changes: False
Auditors/source labels: ["A01"]; []
Adjudication: A01 META-01 admits reading supplied checker source before the formal pre-check plan. It still writes a distinct Groebner table and direct-event strategy implementation.
Disposition: Record source exposure; do not treat its model/prompt independence as blindness proof or discard the successful independent algorithmic checks.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "01a874b1cc6b957d09ad42e1db942fa49faccb4fd1a821b79fe7e9e268d1eed2"}, {"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "497cc0d8eb32b2e985251800617d4aaecaecaa0206d5497e2b1afe8045011bb1"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-003: A06 modular checks reuse exact multiplication table and normalizer

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; []
Adjudication: MULTI is derived directly from cglib_audit.MULT; modular Bell/word products call L.canon,L.star,L.wmul. Changing Fraction scalars to residues breaks rational-accumulation correlation, not relation-table or word-semantics correlation.
Disposition: Credit modular corruption controls only with shared-table/shared-normalizer qualifier. A03/A04 independent prime specializations and fresh Fp2 matrices supply different correlation controls.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_negative_controls.py", "sha256": "f5934f64b1058a5a9798ac3cfd6323d66483d03f0a00106c72ec6e6dd88d548d"}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/cglib_audit.py", "sha256": "f5736db1e42d4ed4bd5f843d4ccf29e089296b63640adedd277ba7a5b0ee6822"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-004: A06 claimed abelianization control is not abelianization

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; []
Adjudication: commutative_canon counts each (r,k) occurrence rather than adding exponents and drops multiplicities; it also orders generators incompatibly with its target. It maps U0*U0 to U0. True quotienting of a genuine identity must preserve that identity.
Disposition: Withdraw control_commutativisation_detected as evidence. Replace with injected noncommutative commutator that vanishes after proper abelianization. No frozen scientific edit.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_negative_controls.py", "sha256": "f5934f64b1058a5a9798ac3cfd6323d66483d03f0a00106c72ec6e6dd88d548d"}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R07_chk_negative_controls.txt", "sha256": "32f5bb9a3d4120908a5fe4970b6dafebefc8c6d3bc123f2cb34ec6e9ea688474"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/a06_commutativization.json", "sha256": "186b3c39061ee8fa2de8637810a1430beb9455600315844aa5e2eb0f00991f0c"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-005: A06 concrete word evaluator reverses factor order

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A06"]; []
Adjudication: word_matrix multiplies each factor on the left. In a two-dimensional exact-order-five numerical representation, a synthetic U0 U2 word differs from intended order by 0.6633436854000504. All 164 frozen raw monomials contain at most one operator per party and are unaffected. The separate high-precision matrix script repeats the same left-multiplication pattern and shares this generic-order limitation.
Disposition: Change left multiplication to right multiplication in future auditor code and add same-party synthetic-word tests. Keep frozen concrete SOS diagnostic, but do not credit the evaluator as a generic order-semantic check.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_matrix_falsification.py", "sha256": "f258ecb531ba16aafd11f7b8f822ff1dcf5d92d807d7c5b58f291d42f7b4ab06"}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_hiprecision_residual.py", "sha256": "2088a73a9609480dbaa2618c1731447e8eac5cbbb63992c4b84feb8c5c5c041b"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/a06_matrix_order.json", "sha256": "b95719dd5d57494af244a6c7c17bd14646cfada22930579dc18ecf3691f8f9dc"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-006: 17, 273, 337 and 1681 word counts measure different sets

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A06", "H01", "BASE"]; []
Adjudication: 17 is final nonzero support after exact cancellation; 273 is actual touched union; H01 second route retains 64 zero Fourier-target slots giving 337; 1681 is full Q*Q Gram universe. A06 sparse W removes exact zeros but separately records 273 touched words.
Disposition: Do not treat count differences as omitted residuals. Keep labels distinguishing touched, surviving, zero-target and full-basis sets.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R01_chk_sos_identity.txt", "sha256": "9d8af31407c657f9dbe157d8da705f3144941330302cc00cc2ef46eb861d975e"}, {"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/RUN_RECEIPTS/R17_word_counts.txt", "sha256": "a0232663723642bef6301bd56466933c590897169387071fb26259878653230a"}, {"path": "work/expanded/H01_Web6Pro_independent_audit/CGLMP5_independent_audit/crosscheck_results.json", "sha256": "9cec9249955ae4b77ef1ee20096cbe69fe93757c7d4aa569d50c1bec2daa0d14"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-007: A07 archived rational SOS path is a failed implementation

Primary class: DUPLICATE_OF_B-S25
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: Archived rational RHS loops only each monomial and adds coef at word*word-adjoint, omitting weights, coefficient products/conjugation and cross terms. Its own receipt is FAIL with one RHS word and 17 residuals. This is not a failed baseline certificate.
Disposition: Preserve as failed development evidence; exclude from successful exact checks. Final integer source has full cross terms and succeeds on fresh replay.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_independent.py", "sha256": "b02785106edda308ffaffe72116882a696278611dd72bf5e8922e89f7ed1259f"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_receipt.txt", "sha256": "462f2128142e39998c9c7b0c19ed59369b0c4a45a931d5f98564f8ae9f72d7e0"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/C_summary.json", "sha256": "87e364f4d846189e586f245debc8384cdcb9bef77526c964958c07a51234e228"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/A07_exact.json", "sha256": "ba24c4f9f4eb50df40f7b6cddf2e0698dd80f0ac121d755b4a7ea0896829fa1d"}, {"path": "outputs/RUN_RECEIPTS/nc/A07_exact.replay_meta.json", "sha256": "65f9ae6f9bfbe3263713ca4c12b2cb2125ceedec778035ceabe57aff3a4beb0b"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-008: A07 adjoint probe crashes after partial useful numeric output

Primary class: DUPLICATE_OF_B-S25
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: Four variant computations finish and distinguish coefficient conjugation and cross terms, but final display loop destructures a word as w,_ and crashes on the empty word. No completed end-to-end run or exact proof credit is justified.
Disposition: Retain partial numeric evidence only; fix display iteration and explicit exit/status reporting in future audit package. Exact integer replay is decisive separate evidence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_adjoint_convention_probe.py", "sha256": "015f742cf327a615e9b3ca0ee76b36230297c967de62a365fee497fcbaf38c3e"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_probe_receipt.txt", "sha256": "134d8939805992fd030f62a7878e2233897c2b75be263432282404b6d2f135ed"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-009: A07 earlier cyclotomic construction bugs are historical harness defects

Primary class: DUPLICATE_OF_B-SD04
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: Reported earlier unreduced z^18/z^19 and unscaled cubic additions were field-engine defects. Final archived routines visibly perform proper reduction/scaling, but those old source versions are not all preserved.
Disposition: Attribute to auditor, not frozen coefficient table; do not claim direct replay of unarchived old versions. Final field-gate output and independent replay are retained.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_independent.py", "sha256": "b02785106edda308ffaffe72116882a696278611dd72bf5e8922e89f7ed1259f"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-010: A07 earlier basis and wrap-phase bugs corrected in final integer path

Primary class: DUPLICATE_OF_B-SD06
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: Comments and ledger describe b=2 parsed as x instead of x^2 and omega^(-k) encoded as zeta^(-k) instead of zeta^(-4k). Final code uses repeated x multiplication and phase -4k; fresh integer replay has zero residual on 273 words.
Disposition: Retain as auditor development defects with final successful replacement; no central repair.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_sos_exact_integer.py", "sha256": "0bd748964bce3df7254cc5a202bd1d7e90f220acf9a05d38a7fdd1e245668c6c"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_exact_receipt.txt", "sha256": "2f588309f6dcd27fb4ac09d7c4de533df6cd95209323537331506b3a62246f68"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/A07_exact.json", "sha256": "ba24c4f9f4eb50df40f7b6cddf2e0698dd80f0ac121d755b4a7ea0896829fa1d"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-011: A07 earlier random-unitary and cross-commutator bugs corrected

Primary class: DUPLICATE_OF_B-SD08
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: Archived source documents earlier Hadamard product instead of matrix multiplication and comparison of operators instead of commutator. Final source uses q@diag and tensor commutator, with assertions.
Disposition: Credit final source/receipt only; do not count old failed implementations as independent confirmations.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/cd_noncommutative_and_positivity.py", "sha256": "0bb0751455ff82bac9d4dd41159b1e364ec2887485b106f8f42d4c4ee58fadef"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-012: A07 C06 overstates direct SOS matrix dimension coverage

Primary class: MISREPORT_OR_REJECTED_FINDING
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: Only d=5,10,15 (nine cases) evaluate SOS. d=20,25 (six cases) assign residual=NaN and test Bell minimum eigenvalues and generator relations. The ledger labels C06 identity tests at all five dimensions. CD receipt is a tail, not full transcript.
Disposition: Separate nine actual SOS evaluations from six Bell-only diagnostics; retain max direct residual 2.0589752126226678e-11 as numerical, not exact evidence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/cd_noncommutative_and_positivity.py", "sha256": "0bb0751455ff82bac9d4dd41159b1e364ec2887485b106f8f42d4c4ee58fadef"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/CD_receipt.txt", "sha256": "456e5cd4779abf2ec33e57d1b123b3658e94ae0de8acc60c82aaaf1783c7597f"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-013: A07 compact verification does not establish Gram-data consistency

Primary class: DUPLICATE_OF_B-S24
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: N1 says compact anticommutator checking covers the same Gram parametrization, but only Q basis matching and supplied Gram checker replay are independent of its compact route. No independent E,H,L,D-to-R equality was checked by A07.
Disposition: Accept Gram bypass for compact theorem proof; withdraw independent Gram-consistency coverage. Other audits separately verify those data and this lane does not reopen compact proof.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/FINAL_AUDIT_REPORT.md", "sha256": "4f6465c63d7886f8823047b031021f5584fe27d3836d0435269062f6b6fa7fe0"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-014: A01 relabel negative control rejects duplicate support before identity

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A01"]; []
Adjudication: A01 generator_relabel case is rejected for a duplicate polynomial word, so that case tests schema uniqueness, not necessarily the semantic identity response to a support-preserving relabel.
Disposition: Limit credit to parser detection. A02 nonduplicate relabel and A05 full-R relabel separately test semantics.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A01_5p6Sol_A1v2/CGLMP5_A1v2_AUDIT_OUTPUT/RUN_RECEIPTS/mutation_controls.stdout", "sha256": "4e7ba372d6e25db9fcb39a5b069d78a2dfae8ec1751dfdbb9fb1326b29da3148"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-015: A03 and A04 initial malformed fixtures abort before controls

Primary class: DUPLICATE_OF_B-S26
Frozen theorem changes: False
Auditors/source labels: ["A03", "A04"]; []
Adjudication: Both initially assume a dense first polynomial coefficient has a zero numerator. StopIteration prevents malformed-case execution. Later fixtures choose existing zero coordinates.
Disposition: Exclude failed attempts from mutation success counts; credit corrected final receipts only. Correlated fixture misconception illustrates why receipt inspection matters.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/harness_revisions.md", "sha256": "43337842e050cc8509d66e4f920ba036b77f2e20b77e8f71a383dc808e6c7813"}, {"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/mutations.attempt1.stderr.txt", "sha256": "a806a45d556d12e18e925fb817c32cc75f97d3521058388edc209ecc11377be2"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/auditor_development_corrections.md", "sha256": "e64ca27d2b7f82ac3525d0fb10ae7d21fc313e1155c52d1889e7ba1fd65edc05"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/independent_controls.initial_failed.stdout.txt", "sha256": "02d3ff88ca822a2e423764ffa8dd0dc1fcb8723e5a4952bb2b53ef701ee2f52c"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-016: A04 exhaustive coefficient sweep is exact delta testing

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["A04"]; []
Adjudication: After timeout, 164 controls evaluate exact perturbation deltas, with one full mutated-term expansion crosscheck per square. These are not 164 full end-to-end verifier invocations. Formula includes four linear cross terms plus 2*d*delta^2.
Disposition: Credit exact algebraic sensitivity sweep with correct scope; retain timeout history; no baseline defect.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/INDEPENDENT_CHECKS/run_controls.py", "sha256": "5d4d40b646fe81803077dc6e35e109932c800ba09f607336ebbf8929f019b98e"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/auditor_development_corrections.md", "sha256": "e64ca27d2b7f82ac3525d0fb10ae7d21fc313e1155c52d1889e7ba1fd65edc05"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/independent_controls.timed_out.stdout.txt", "sha256": "093faa21e837610b29b3167e91fa51b3b985d563fe3c06fdcda6eb24caecd6fd"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-017: A04 first new-support author rejection was invalid invocation

Primary class: DUPLICATE_OF_B-S27
Frozen theorem changes: False
Auditors/source labels: ["A04"]; []
Adjudication: Initial harness supplied positional JSON to --root verifier; nonzero exit did not establish mathematical rejection. Corrected invocation repeats run and reaches ArithmeticError residual rejection.
Disposition: Use corrected receipt only; preserve invalid invocation as auditor bug, not theorem evidence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/auditor_development_corrections.md", "sha256": "e64ca27d2b7f82ac3525d0fb10ae7d21fc313e1155c52d1889e7ba1fd65edc05"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.invalid_author_invocation.json", "sha256": "0e4f403a390e4291782622370fe912c4fc6029fb2f0260fd9adb711013cece5b"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/meta_exact.json", "sha256": "e4498b12d2fddd9a31e632d07ee0ddfd71dd3e54d5642abe4726e9a5fe1c4870"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-018: Shared algebraic presentation does not require irreducibility for zero implication

Primary class: DUPLICATE_OF_FIELD-002
Frozen theorem changes: False
Auditors/source labels: ["BASE", "A01", "A02", "A03", "A04", "A05", "A06", "A07", "H01", "H02"]; []
Adjudication: All exact engines use the printed actual-number relations. A zero produced solely by sound polynomial identities evaluates to zero in the actual embedding whether or not the quotient basis is minimal/faithful. Branch and positivity remain separate obligations.
Disposition: Do not demand irreducibility as a missing upper-bound premise; explicitly preserve common-relation dependence and defer actual-embedding proof to root lane.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/INDEPENDENT_CHECKS/sos_branch/SOS_BRANCH_REPORT.md", "sha256": "17f0279f294684a46784be8b9abdbc57dda4df8ac0ee94b11396f16093e3f91e"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-019: Same-party noncommutation preserved by all inspected normalizers

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["BASE", "A01", "A02", "A03", "A04", "A05", "A06", "A07", "H01", "H02"]; []
Adjudication: Stack separation, adjacent cross-party interchange, repeated run contraction, and expanded-letter representations all preserve local relative order and only reduce equal-generator powers mod five. Fresh test exhausts 0..4 factors over 16 nonzero syllables plus 5000 long/cancellation cases.
Disposition: No scientific normalizer repair proposed. Finite tests supplement direct source/analytic soundness; do not claim formal verification.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/verify_independent.py", "sha256": "8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/cross_audit_normal_forms.json", "sha256": "949e1d9f85e28f5f559676104a9679fbeda1e6f67d0bb791c547dace8ecf1109"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-020: Fresh Fp2 matrices independently break field and word implementation correlation

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["PHASE_B"]; []
Adjudication: 102 Hermitian-unitary matrix specializations at eight primes use actual Frobenius conjugation, independent direct scalar evaluation, literal-event spectral projectors, no quotient arithmetic and no word reduction. Baseline exact residual zero; each of four targeted corruptions detected in all 102.
Disposition: Accept as exact finite-characteristic correlation control, not characteristic-zero proof or positivity evidence.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "outputs/INDEPENDENT_CHECKS/nc/finite_field_matrix_attack.py", "sha256": "0f95bf95784a37088110795385bdf3ba5a98702d645f9dd50293ae48424b1b40"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/finite_field_matrix.json", "sha256": "12f8100cb353e29ee7b7266f5c1a8852f57d3649c8d87526402c7f3d07185757"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-021: Fresh matrix-control initial seed accidentally commuted

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["PHASE_B"]; []
Adjudication: Initial generator sampler asserted noncommutation on a random finite-field pair that accidentally commuted. It stopped before issuing baseline verdict. Final sampler rejects such a fixture and deterministically advances seed.
Disposition: Preserve failed attempt; count only accepted noncommuting cases with recorded final seed. This is fixture coverage, not certificate failure.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "outputs/INDEPENDENT_CHECKS/nc/finite_field_matrix_attack.attempt1.py", "sha256": "1bd7b57941f5e50c13ab6567877c8eec7b93f5ef69f049cdd6b7fe701b8bd74e"}, {"path": "outputs/RUN_RECEIPTS/nc/finite_field_matrix.attempt1.stderr", "sha256": "dd44e1b21f31915e6075f4051605dd5e43ef69cd8051f411a66b52edfc221d24"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/finite_field_matrix.json", "sha256": "12f8100cb353e29ee7b7266f5c1a8852f57d3649c8d87526402c7f3d07185757"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-022: Fresh generic order-control initial fixture accidentally commuted

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["PHASE_B"]; []
Adjudication: All normalizer comparisons completed, then random negative-control matrices commuted and assertion correctly stopped the run. Replaced with fixed visibly noncommuting matrices; repeated entire test.
Disposition: Count final full successful run only; retain failed fixture transcript.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "outputs/INDEPENDENT_CHECKS/nc/cross_audit_normal_forms.attempt1.py", "sha256": "d51359ce7d70830c60155516b52a674b6784c9f649378f0b39fdcb002874cda2"}, {"path": "outputs/RUN_RECEIPTS/nc/cross_audit_normal_forms.attempt1.stderr", "sha256": "09c3ac0768f8f22b09a5ddb69b9faab50c554ab681795762246e04120d7f1542"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/cross_audit_normal_forms.json", "sha256": "949e1d9f85e28f5f559676104a9679fbeda1e6f67d0bb791c547dace8ecf1109"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-023: Fresh universal bridge cross-review found no new route

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: ["PHASE_B"]; []
Adjudication: Reviewed V*V-only rewrite, typed block structure, fixed common J and normalized positive-functional pullback. Replayed formal W*=W,W^2=I and exact positive compression-defect example; no extra VV*=I or multiplicative-compression assumption enters.
Disposition: No bridge change requested from NC cross-review; analytic reasoning and finite controls remain distinct.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "outputs/INDEPENDENT_CHECKS/bridge/formal_isometry_bridge.py", "sha256": "7544f6649130787b7383bd5d31285a3ad86a5085eb2c232a954ccc948d2ac1ff"}, {"path": "outputs/INDEPENDENT_CHECKS/bridge/exact_common_space.py", "sha256": "2b1cad53a8acac603b1655ae0a29363cb2dbe73d096da4003891713c0c3e463c"}, {"path": "outputs/INDEPENDENT_CHECKS/bridge/compression_product_attack.py", "sha256": "e25f050ee86b9ef49abf02fd7dbb240ce81bde167fb62608eaac0a18611d3bb8"}, {"path": "outputs/lanes/bridge/ANALYTIC_UNIVERSAL_BRIDGE.md", "sha256": "ee155d02fa03b8a006df63abe49ee512c8f79b58c1572c46cfef8664e538f7f5"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/bridge_formal_review.stdout", "sha256": "3f6d617a247c5a4d238e31d648e59cdcfb402d53fce38968ec73dcff1b5763df"}, {"path": "outputs/RUN_RECEIPTS/nc/bridge_compression_review.stdout", "sha256": "e4f60d2fc2859df42da33444a45648e809e2372b254039bb3562ecb2e20cd6b3"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## NC-024: A07 abandoned modular-size bound aborts and lacks valid coordinate bound

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["A07"]; []
Adjudication: Size receipt aborts at the 4300-digit integer-string cap after reporting the LCM. The unexecuted proposed bound treats L times residual as a rational integer, ignores basis-coordinate versus embedding magnitude and x-squared size, and does not correctly justify triple-product denominator clearing. A concrete weighted coefficient product retains denominator 5 after multiplying by L. Final A07 proof instead uses correct L cubed scaling.
Disposition: Exclude abandoned size-bound route from proof coverage; preserve partial structural/LCM observations only. No effect on successfully replayed final integer proof.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/c_size_analysis.py", "sha256": "25b1622e6daf5826b8f5855f4bdfff0d11702bf4b148d9543125516829740bf1"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/C_size_receipt.txt", "sha256": "120ed3ae5df0b47f85810baec2b4ca72420620785ae5c6dbcbb484e334316756"}]
Independent reproduction: [{"path": "outputs/RUN_RECEIPTS/nc/a07_size_bound.json", "sha256": "846b4ddcb72253a98d4810c516e9b4cb5cc8890d249fde4be2b2d02747295758"}]
Supplementary deduplicated adjudications: []
Lane provenance: lanes/nc/findings.json (SHA-256 b42d396d0dad70de63e004f5f54a07fdd24d01b141d6725d0e55e47906a3002a)

## B-AT01: Literal probability convention and full target linkage survive

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A01:A-01/A-02", "A02:A-001..A-005", "A03:A01..A03", "A04:A-01..A-04", "A05:A1/A2", "A06:A-001..A-005", "A07:A-01..A-07", "H01:§2/events_and_fourier"]
Adjudication: Accept exact event-wise target identification, local bound2, D shifts and Fourier sign; no scientific revision.
Disposition: Accept exact event-wise target identification, local bound2, D shifts and Fourier sign; no scientific revision.
Limitations: Prior source comparisons are corpus evidence; this lane made no external source/novelty search. Deterministic agreement alone is not substituted for100 coefficient comparisons.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/exact_linkage.json", "sha256": "829b506d6b8685115cf2ce376857d2bf195c9e2231e097157720b0acd6afefeb"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT02: A06 NLB-5 labels correct standard normalization a defect

Primary class: DUPLICATE_OF_B-S16
Frozen theorem changes: False
Auditors/source labels: []; ["A06:NLB-5", "A06:A-003"]
Adjudication: Reject defect classification; k=0,1 is correct stated standard normalization. Summing reflected pairs through k=4 doubles the functional.
Disposition: Reject defect classification; k=0,1 is correct stated standard normalization. Summing reflected pairs through k=4 doubles the functional.
Limitations: Optional explanatory note is harmless; it repairs no theorem error.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/exact_linkage.json", "sha256": "829b506d6b8685115cf2ce376857d2bf195c9e2231e097157720b0acd6afefeb"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT03: Full25-dimensional exact strategy and all28 saturation vectors survive

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A01:F-01..F-03", "A02:F-001..F-006", "A03:F01..F03", "A04:F-01/F-02/M-02", "A05:F1/F2/PB-F01/PB-D05", "A06:F-001..F-006", "A07:F-01..F-05", "H01:§7/exact_attainment"]
Adjudication: Accept exact physical attainer, legal normalization, gamma linkage and full-coordinate saturation; no theorem change.
Disposition: Accept exact physical attainer, legal normalization, gamma linkage and full-coordinate saturation; no theorem change.
Limitations: Quartic-u/cubic-mu/quadratic-i engine is fresh code; same actual algebraic numbers and statement remain shared. Denominator positivity also checked by field peer; analytic μ>3,0<f1,f2<1 gives D>4.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/exact_linkage.json", "sha256": "829b506d6b8685115cf2ce376857d2bf195c9e2231e097157720b0acd6afefeb"}, {"path": "outputs/RUN_RECEIPTS/attainment/exact_linkage_replay.json", "sha256": "19859259b0d22cff41afb104e52aa580854dbb8e919a6a689ae79bd30846ab11"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT04: A07 first strategy harness omitted D shifts and mis-tested cross-party commutation

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: []; ["A07:F-01/F-02 first attempt", "A07:report§7 own bugs"]
Adjudication: Preserve first failed attempt, discard its operator mismatch as auditor-generated; corrected v2 reproduces attainment.
Disposition: Preserve first failed attempt, discard its operator mismatch as auditor-generated; corrected v2 reproduces attainment.
Limitations: First version also reverses party tensor order on odd edges. It is not evidence against frozen theorem.
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/f_strategy_encoding.py", "sha256": "9a31b5b8f146793668c4543fe4906cae659fca4ffd8937f5349fb51b1a4c364d"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/RUN_RECEIPTS/F_receipt.txt", "sha256": "cc3c69e520c960a914f6d724891cacf6866f4deea9e6737251ec6191ede69f2b"}, {"path": "outputs/RUN_RECEIPTS/attainment/a07_v2_replay/stdout.txt", "sha256": "ac94072f90d9cc138ad7a054b9fdf01495eb5e421bc13ede70c59435be0367e0"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: [{"alias": "B-SD01", "adjudication": "Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [86]}], "source_labels": ["A07 bug1"]}, {"alias": "B-SD02", "adjudication": "Disclosed auditor-development defect. Historical intermediate source versions are not all preserved; delivered corrected code/receipts only support their actual scope. No frozen theorem defect follows.", "evidence": [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/ATTACK_LEDGER.md", "sha256": "9f0936f0ed25dc30141c6cd23e072902c2f3fd96a1e0cc28443a76b7b713b3ad", "lines": [87]}], "source_labels": ["A07 bug2"]}]
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT05: A07 generic tensor-order error hidden by exact symmetry of optimizer fixture

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: []; ["A07:F-02/F-04/F-05", "NEW:generic tensor-placement meta-test"]
Adjudication: Repair A07 generic build_B odd-edge Kronecker ordering and add generic event-matrix negative control. Keep its special-fixture attainment result:625 entries agree exactly.
Disposition: Repair A07 generic build_B odd-edge Kronecker ordering and add generic event-matrix negative control. Keep its special-fixture attainment result:625 entries agree exactly.
Limitations: Initial suspicion of source/receipt mismatch was rejected after replay. Wrong formula differs from literal target by Frobenius7.2129177491972065 on a generic legal PVM; correct ordering differs9.89e-15. Audit code issue, not theorem issue.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/a07_tensor_control.json", "sha256": "d0abf498c7ab1c888baad7a2aef6c46fc9e6f6933810b56ca6bf507e4eb7b911"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT06: A06105/400 supplementary random samples are incomplete purported PVMs

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: []; ["A06:H-002", "A06:chk_povm_bridge random-search branch"]
Adjudication: Replace first-five-rank-one truncation by complete outcome grouping; validate completeness before recording samples. Discount105 original invalid samples.
Disposition: Replace first-five-rank-one truncation by complete outcome grouping; validate completeness before recording samples. Discount105 original invalid samples.
Limitations: Original-seed replay and repaired candidates both maximum1.460443938980493; valid POVM branch supplies maximum. Independent A06 spectral-unitary dimension scan is valid and unaffected.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/a06_search_health.json", "sha256": "ad1afbbc0d45c13eb7fdec058c9e1973ca652450fc1f6b81f7ce70d325a30928"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT07: A07 product-state and fixed-measurement searches have sharply limited falsification power

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A07:H-01"]
Adjudication: Describe searches accurately: product pure states; product mixed rho⊗rho;400 product-state phase trials; hill climb only real Schmidt amplitudes at fixed Fourier measurements. Retain12 generic spectral tests.
Disposition: Describe searches accurately: product pure states; product mixed rho⊗rho;400 product-state phase trials; hill climb only real Schmidt amplitudes at fixed Fourier measurements. Retain12 generic spectral tests.
Limitations: Valid product-state samples cannot violate local bound2 and are not broad searches for entangled quantum advantage. The distinct truncated-PVM failure is B-AT17; singular rank-one POVM normalization is coordinator B-E02, also present in h_numeric_kill.py lines39–44.
Frozen bytes / raw evidence: [{"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/h_numeric_kill.py", "sha256": "0a2d747fb91f6e39765c482ffed8a282130f020c1d7577f049267d8c084ffd3d"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT08: A03 optimizer precision-loss and highest floating overshoot are properly limited diagnostics

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A03:H03/H06/M04"]
Adjudication: Retain eight failed BFGS starts and later derivative-free recovery distinctly; highest exact-binary-float phase endpoint lies below μ by1.75588767996e-16 at70/110 digits.
Disposition: Retain eight failed BFGS starts and later derivative-free recovery distinctly; highest exact-binary-float phase endpoint lies below μ by1.75588767996e-16 at70/110 digits.
Limitations: This is high-precision diagnosis, not a directed-rounding certificate. Exact bound does not follow from optimizer success.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/a03_near_replay.json", "sha256": "5dec2e298f9b7c8ba910d2f213ffb765f86f8ac4978ac00ae1f24cc00908d709"}, {"path": "work/expanded/A03_6Pro_A1v2/CGLMP5_A1v2_AUDIT/RUN_RECEIPTS/harness_revisions.md", "sha256": "43337842e050cc8509d66e4f920ba036b77f2e20b77e8f71a383dc808e6c7813"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT09: A04 exact-rational envelopes correctly cover nearby physical representatives

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A04:H-02/H-04"]
Adjudication: Accept all six exact rational envelopes, independently recomputed with Gaussian integers/full tensor Bell matrices; minimum certified gap9.86874822834e-16.
Disposition: Accept all six exact rational envelopes, independently recomputed with Gaussian integers/full tensor Bell matrices; minimum certified gap9.86874822834e-16.
Limitations: The explicitly normalized representatives are different objects from raw floating effects. No claim of exact feasibility of the raw arrays; no inference of global bound from finite candidates.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/a04_rational_replay.json", "sha256": "c184e5588ec827445715f67aec281681797fc08c9df343c7fffd7d7549040605"}, {"path": "outputs/RUN_RECEIPTS/attainment/a04_integer_envelopes.json", "sha256": "9228eea15029b951293053e618785bd282655539ccac2959204562a263bfcd74"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT10: A05 strongest apparent excess is explained by nonunitary stored bases and strengthened by exact enclosure

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A05:H1/H2/H3/H4/H5/STR-M8"]
Adjudication: Accept original90/130-digit repaired-candidate diagnosis with its caveat. New rational physical representative has rigorous gap≥3.3512604648438227e-21 and correction bound1.65e-76.
Disposition: Accept original90/130-digit repaired-candidate diagnosis with its caveat. New rational physical representative has rigorous gap≥3.3512604648438227e-21 and correction bound1.65e-76.
Limitations: Raw imported matrices exceed μ by9.806566226e-15 but violate exact unitarity/completeness; QR changes them. New enclosure is of an explicitly defined nearby normalized strategy, not the original floating array.
Frozen bytes / raw evidence: [{"path": "work/expanded/A05_Dot_Blind/CGLMP5_PHASE_A_AUDIT/output/RUN_RECEIPTS/strategy_branch/refine_candidate.json", "sha256": "3dff80f210ac2bf6b8ab22cdfd6fea5922f75fed1402643fd367936c06a32f7a"}, {"path": "outputs/RUN_RECEIPTS/attainment/a05_integer_envelope.json", "sha256": "7b488f6e9f15179fb373c843077dcd55f5a53c7e87685cb9d647f5ed448e1458"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT11: A06 optimizer omits termination/candidate evidence and overstates search scope

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: []; ["A06:H-004", "A06:H-007"]
Adjudication: Record all31 terminations, preserve candidate arrays, label finite rank-one-PVM chart search. Fresh replay:0/31 success, best3.0157104755226802; repaired rational representative has gap≥1.1934973389758194e-15.
Disposition: Record all31 terminations, preserve candidate arrays, label finite rank-one-PVM chart search. Fresh replay:0/31 success, best3.0157104755226802; repaired rational representative has gap≥1.1934973389758194e-15.
Limitations: Historical candidate vector was not retained; fresh library-dependent replay is not bitwise recovery of original endpoint. Rank-one d5 fixed spectra do not cover every degenerate five-outcome PVM. No numerical search is a universal bound or guaranteed counterexample finder.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/a06_optimizer_replay.json", "sha256": "26e5d56468f418ef59cf264211705f2339bfe71a4d5a3a7a3e83c7afb7992bde"}, {"path": "outputs/RUN_RECEIPTS/attainment/a06_integer_envelope.json", "sha256": "15c185874d91dc47762ea3ee170b3a2f7dbacc516ce5fa74986ca71092962709"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT12: Numerical SDP/non-SDP evidence cannot be counted as universal certification

Primary class: MISREPORT_OR_REJECTED_FINDING
Frozen theorem changes: False
Auditors/source labels: []; ["A04:H-03", "A05:H6", "A06:H-007", "A01:META-02"]
Adjudication: Accept A04 ADMM as independent numerical diagnostic only (81 words,1681 moments, residual7.83e-14). Reject A06 claim random scans/local maximization are representation-independent upper-bound checks or strictly stronger than SDP. Exact independently verified SOS is a valid supersession reason.
Disposition: Accept A04 ADMM as independent numerical diagnostic only (81 words,1681 moments, residual7.83e-14). Reject A06 claim random scans/local maximization are representation-independent upper-bound checks or strictly stronger than SDP. Exact independently verified SOS is a valid supersession reason.
Limitations: A04 floating primal/dual near μ contradicts an unqualified claim that all feasible NPA levels must be non-tight, but is not itself a certified tightness theorem. No installed solver is needed for exact SOS correctness.
Frozen bytes / raw evidence: [{"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/RUN_RECEIPTS/npa.json", "sha256": "fd05e2ec3658d46d856eec35665d333de5c512840bdb0588c58503a187e8a11d"}, {"path": "work/expanded/A04_6Pro_ExternalPrompt/CGLMP5_PHASE_A_AUDIT/INDEPENDENT_CHECKS/run_npa.py", "sha256": "1419003fdfe07df5c180840fa0ef201e4cfbc88206a1465affa91fc56f927c88"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT13: Historical lower-bound and kill-test evidence has limited independent ancestry

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["H02:§3/§4/§5/T5/T6", "H03:physical state and phase controls"]
Adjudication: Treat H02 as historical report, H03 as author-engine mutation source. H01 raw code supplies separate exact implementation, but shares algebraic relations/target definition. Do not count this as fresh full-theorem independent discovery.
Disposition: Treat H02 as historical report, H03 as author-engine mutation source. H01 raw code supplies separate exact implementation, but shares algebraic relations/target definition. Do not count this as fresh full-theorem independent discovery.
Limitations: H02 target polynomial/value were already supplied; unguided reconstruction only lower-bound partial. H03 imports verify_independent; cannot be credited separate arithmetic.
Frozen bytes / raw evidence: [{"path": "work/corpus/CGLMP5_PHASE_B_FINAL/historical_pre_phase_a/H02_INTERNAL_POST_ONESHOT_VERIFICATION_RECORD.md", "sha256": "e84dbd033d581fea965c2fb016218f8e6e9eb75ad7e6cc3ea64830f6a6672b02"}, {"path": "work/corpus/CGLMP5_PHASE_B_FINAL/historical_pre_phase_a/H03_original_kill_tests.py", "sha256": "ba178151141acaf84891ef0610b2d3027c135e08a057c62b53151f373ecac8f7"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT14: A0649-digit check actually compares a binary64 prefix

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: []; ["A06:H-006"]
Adjudication: Replace float conversion/startswith with retained arbitrary-precision root string and explicit digit check; downrate original claimed49-digit test.
Disposition: Replace float conversion/startswith with retained arbitrary-precision root string and explicit digit check; downrate original claimed49-digit test.
Limitations: The actual printed μ digits are corroborated elsewhere; this is weak auditor test, not incorrect mathematical value.
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_numerical_kill.py", "sha256": "eb2abe47fdbcff84bf39c9a40b2284e6679befaa84cd0253c3b21ac62f046750"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT15: A06 full-coordinate check uses a valid explicit leakage guard

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A06:F-003"]
Adjudication: Accept check despite only accumulating diagonal entries: it separately rejects every nonzero individual off-diagonal contribution through B_sends_diagonal_to_diagonal and gates exit on that flag.
Disposition: Accept check despite only accumulating diagonal entries: it separately rejects every nonzero individual off-diagonal contribution through B_sends_diagonal_to_diagonal and gates exit on that flag.
Limitations: New full-matrix check provides less specialized corroboration. Some positive-state flags are reported but not all gated in A06 aggregate ok; peer/new analytic positivity closes present frozen strategy.
Frozen bytes / raw evidence: [{"path": "work/expanded/A06_DS_V4p1_Flash_ExternalPrompt/cglmp5_audit/PHASE_A_OUTPUT/INDEPENDENT_CHECKS/chk_attainment.py", "sha256": "8600b9cc53fc4a8ff5d660460ebeffe72ec5d748d0a3308bfbafddd41a52e7e1"}, {"path": "outputs/RUN_RECEIPTS/attainment/exact_linkage.json", "sha256": "829b506d6b8685115cf2ce376857d2bf195c9e2231e097157720b0acd6afefeb"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT16: Valid numerical searches supply falsification diagnostics only

Primary class: BENIGN_ACCEPTANCE_OR_SCOPE_LIMIT
Frozen theorem changes: False
Auditors/source labels: []; ["A01:H-01..H-04", "A02:H-001..H-004", "A03:H01/H02/H04/H05", "A04:H-01", "A06:H-001/H-003/H-005/H-008"]
Adjudication: Retain valid PVM/POVM spectra and near-optimal searches as convention/falsification checks; never infer a global or dimension-independent upper bound from them.
Disposition: Retain valid PVM/POVM spectra and near-optimal searches as convention/falsification checks; never infer a global or dimension-independent upper bound from them.
Limitations: A01/A02 use valid complete higher-rank projectors and normalized general POVMs. A06 spectral-unitary scans are separate from its defective truncated-effect search. A02 exact state optimization wording means numerical eigensolver for fixed effects, not certified algebraic optimization.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/exact_linkage.json", "sha256": "829b506d6b8685115cf2ce376857d2bf195c9e2231e097157720b0acd6afefeb"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/PROOF.md", "sha256": "a2080e3685bfdc8e899d471f39a15a4ed6cf87767a9357703d2c065a8dd2b4ee"}, {"path": "work/expanded/CGLMP5_PHASE_A_INPUT_v1.2/PHASE_A_BLIND_AUDIT/scientific_payload/SOS14.json", "sha256": "1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-AT17: A07 first-five truncation makes all d6/7 purported projective samples incomplete

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: []; ["A07:H-01 random projective trials"]
Adjudication: Discount150 trials each at d6 and d7 as invalid measurements; group every basis column into five outcomes and validate completeness. Distinct from benign product-state restriction B-AT07.
Disposition: Discount150 trials each at d6 and d7 as invalid measurements; group every basis column into five outcomes and validate completeness. Distinct from benign product-state restriction B-AT07.
Limitations: Source rand_povm lines39–44 independently repeats coordinator B-E02 singular rank-five construction; cross-reference B-E02 rather than double-count that separate defect.
Frozen bytes / raw evidence: [{"path": "outputs/RUN_RECEIPTS/attainment/a07_sampling_health.json", "sha256": "08fd5b907c03667e618ee54353636f95233a8410195df72cd71c40723d3b7c98"}, {"path": "work/expanded/A07_SpaceBunny_ExternalPrompt/AUDIT_OUTPUT/INDEPENDENT_CHECKS/h_numeric_kill.py", "sha256": "0a2d747fb91f6e39765c482ffed8a282130f020c1d7577f049267d8c084ffd3d", "lines": "52–67; basis56–59; selection64–67"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/attainment/findings.json (SHA-256 e709457a96cc239c76681939f7c5dc822e88d88ed7fa36b20b45ed91bff28308)

## B-CO01: Phase-B ledger merger initially expected status instead of terminal_status

Primary class: AUDITOR_OR_HARNESS_DEFECT
Frozen theorem changes: False
Auditors/source labels: ["PHASE_B"]; []
Adjudication: Metadata assembly aborted before writing a merged attack ledger because schema lane uses terminal_status while other lanes use status. The explicit missing-status assertion failed closed. Corrected merger accepts either named field and validates all52 terminal routes; scientific scripts and results unchanged.
Disposition: Retain failed assembly attempt and corrected merger; no scientific or baseline change.
Limitations: See scoped evidence
Frozen bytes / raw evidence: [{"path": "INDEPENDENT_CHECKS/coordinator/merge_attacks.attempt1.py", "sha256": "e20cdd4d52e5e9f8057831201c593c437bdd3975c52bbafbe8a3106fb5079de0"}, {"path": "RUN_RECEIPTS/merge_attacks.attempt1.stderr", "sha256": "9e86785d7e087e44fa9aac7d52c4ba5680608e1da25d89c58475ea343267f2e0"}]
Independent reproduction: []
Supplementary deduplicated adjudications: []
Lane provenance: lanes/coordinator/findings.json (SHA-256 37c82e2ef0c004f7eb9f7414163407efe669a5a74080be5ab26c7d8202240e9a)

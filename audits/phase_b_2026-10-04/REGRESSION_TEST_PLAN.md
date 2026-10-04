# Regression plan for an approved future revision

This is a proposed acceptance suite, not permission to alter the frozen archive. Execute in normal Python through the guarded runner; inspect semantic status as well as return code. Preserve inputs, failed attempts and exact command/source/output hashes. A hardening revision passes only if every frozen scientific identity remains unchanged and deliberate corruptions fail for the intended reason.

| ID | Required regression | Expected result / reason |
|---|---|---|
| R01 | Recompute outer, payload and revised-release manifests; retain original bytes and original-to-curated maps | Exact matches, with historical manifest scope explicitly distinguished |
| R02 | Every entrypoint: floats, booleans, duplicate keys, malformed integer strings, NaN/Infinity, missing n/d, wrong vector length, zero/negative denominator | Consistent strict schema rejection before arithmetic; no silent int coercion |
| R03 | Gram Q and compact words: Boolean/integral-float aliases, nonintegral exponents, wrong party/generator, absent fields, integer-string policy | Shared documented schema; test combined preflight plus every consumer |
| R04 | Mutate proof text, theorem id, polynomial order/root, field descriptor, declared support and cached status independently and jointly | Enforced fields reject or are explicitly reported unverified/annotative; receipt never claims a different theorem than actually checked |
| R05 | Benign controls: added explicit zero, unreduced rational, duplicate diagnostic ID, summand permutation, R→iR, R→2R with d→d/4, compatible conjugation | Mathematical invariance retained; any canonical-schema rejection explicitly distinguished from scientific rejection |
| R06 | Compact exact 273-word and full 1,681-word Gram paths; E L→R and H=L D L*; alternate scalar/word engine; proper abelian quotient and injected commutator | All baseline exact residuals zero. Correct quotient preserves true identity; wrong extra commutator detected by NC engine. Finite-field controls remain diagnostic |
| R07 | Largest root and all actual branch signs; rational boxes plus independent Sturm–Tarski/Fraction or Bernstein path; zero/nonreal/negative weight controls | Correct largest branch, every d>1/3000; root-shift control actually reevaluates coefficients; wrong branches lose required positivity |
| R08 | Literal 100 event coefficients, all 625 deterministic assignments, 20 Fourier projectors, full 625 Bell entries, 25 eigenvector coordinates, all 28 saturation vectors, positive normalization/denominators | Exact equality to same target; wrong wrap sign or D shifts reject. Preserve actual embedding map and nonzero cleared state |
| R09 | Fixed common J for both POVM settings; separate complements and Halmos defect construction; zero/rank-deficient effects, unequal dimensions, entangled mixed state; analytic infinite/nonseparable/nonnormal proof | All joint compressions equal original effects; wrong setting-dependent embedding and omitted completion reject. Compression is not assumed multiplicative |
| R10 | Generic noncommuting representations away from Fourier optimizer fixture; correctly ordered same-party words and odd-edge tensor factors; every measurement family complete/positive | Expose tensor-order bugs masked exactly by symmetric fixture; d>5 samples group every column into five outcomes |
| R11 | Real coefficient/weight mutations, dropped block, extra support, phase reversal, lowered bound, invalid state; true sign reversal versus coordinate tripling | Each rejected at intended mathematical invariant, not argument error, duplicate support, timeout or fixture construction failure |
| R12 | Near-counterexamples: preserve raw arrays and optimizer statuses; validate physical constraints; define rational repaired representative explicitly; exact enclosure of its expectation | Raw invalid samples are not counterexamples; repaired representative is a distinct defined strategy; no floating/finite search is a global upper bound |
| R13 | Normal/-O/-OO/environment flag runs; intentional FAIL with exit0; wrong CLI argument; incomplete output and stale receipt | Guard refuses optimized execution; orchestration requires mathematical status and residual; failed/partial run never counted as PASS |
| R14 | Clean relocated replay, version/cwd/seed/source/input hash binding, failure-history retention, source-claim-to-finding coverage and final artifact manifest | Portable and auditable evidence; no unsupported independent-model, novelty, peer-review or full-replay claim |

## Concrete starting points retained in this Phase B bundle

- `INDEPENDENT_CHECKS/replay_guard.py`: records command, flags, source/output hashes and leaves semantic status to the caller.
- `INDEPENDENT_CHECKS/attainment/exact_linkage.py`: fresh characteristic-zero literal/full-space/saturation interface.
- `INDEPENDENT_CHECKS/field/sturm_tarski_weights.py`, `fraction_sign_meta.py`, `review_attainment_field.py`, `gram_elimination_recheck.py`: actual-branch sign and cross-representation/data-path controls (consult lane report for exact commands).
- `INDEPENDENT_CHECKS/nc/finite_field_matrix_attack.py`, `cross_audit_normal_forms.py` and replay wrappers: word-independent matrix and expanded-letter controls.
- `INDEPENDENT_CHECKS/bridge/`: exact common-space, proper-isometry, fixed-state and compression-product controls.
- `INDEPENDENT_CHECKS/schema/`: coordinated metadata/schema mutations and original-auditor component probes.

Frozen input paths referenced by the scripts are retained in the final checkpoint. New future packaging may expose explicit root arguments instead; such adaptation must preserve and record hashes and must not be represented as an unchanged-source replay.

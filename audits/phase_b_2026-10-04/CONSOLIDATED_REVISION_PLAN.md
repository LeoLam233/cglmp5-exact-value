# Consolidated advisory revision plan

Classification: **NONLOAD_BEARING_HARDENING_ONLY**.

This plan was assembled after the deduplicated master ledger and coverage matrix. It is advisory: no frozen v0.1 payload, Phase-A ZIP, GitHub file, branch or release was modified. Preserve the current artifacts as historical evidence; apply any accepted changes only to a separately approved future revision. None of the accepted changes below changes the frozen scientific theorem, its maximum, its certificate coefficients or its physical strategy.

## 1. Central scientific change

**None proposed.** The exact upper-bound identity, actual positive embedding, dimension-independent representation implication, common-space local POVM bridge and full 25-dimensional attainer require no repair on the recorded evidence. Do not replace the theorem with a dimension-five/projective/Fourier-only special case, alter the polynomial/root, or weaken the quantifiers to accommodate an auditor's broken test.

## 2. Verifier/schema hardening

| Change | Exact future files | Reason / master findings | Regressions | Frozen theorem changes? |
|---|---|---|---|---|
| One strict decoder on every mathematical entrypoint | `verify_independent.py`, `verify_sos14.py`, `verify_statement.py`, `validate_integer_encoding.py`; optionally new `strict_schema.py` | B-S01–B-S04: reject duplicate keys, booleans, floats, malformed integer strings and nonfinite tokens before mathematical use; do not rely on separately remembered preflight | R01–R03, R06–R08, R11 | No |
| Validate required structures and Gram Q explicitly | Same four entrypoints; schemas for `SOS14.json`, `EXACT_KERNELS.json`, `EXACT_SOS_CANDIDATE.json`, `POSITIVITY_CERTIFICATE.json` | B-S04–B-S06: syntax traversal alone misses Q and missing members; choose one word-type contract | R02–R03 | No |
| Separate canonical serialization choices from mathematics | `verify_sos14.py`, `validate_integer_encoding.py`, schema documentation | B-S07/B-S10–B-S12: explicit zero, duplicate diagnostic IDs, unreduced rationals, equivalent noncanonical words and harmless rescaling need an explicit policy. Report stored-record and actual-nonzero counts separately | R05, R11 | No |

Do not silently call every equivalent encoding malicious or every benign accepted mutation a mathematical failure. Canonical-format rejection may be a packaging policy; the exact sum remains the scientific object.

## 3. Metadata/provenance binding

| Change | Exact future files | Reason | Regressions | Frozen theorem changes? |
|---|---|---|---|---|
| Bind a checker result to its actual enforced target | `verify_statement.py`, `verify_sos14.py`, `verify_independent.py`, `README.md`; new release-level verification receipt/schema | B-S08: include checker/source version, full input digests, authoritative theorem identifier, polynomial coefficient order, root selector, scalar-basis convention and standard-event definition. Clearly distinguish enforced fields from ignored historical annotations | R01, R04, R13–R14 | No |
| Preserve historical versus current receipts | `MANIFEST.sha256`, `verification/receipts/packaging_identity.json`, README and future audit manifests | B-S31/B-S32: keep original-to-curated maps, required manifest base directory and old failed receipts. Hashes identify bytes, not unseen execution history or external validation | R01, R14 | No |
| Correct audit evidence labels in an appended errata document | Future `PHASE_B_ERRATA.md` pointing to original A01–A07 paths; never rewrite original supplied audit ZIPs | B-S17–B-S29, FIELD-007/008, NC-004/005/012/024, B-E01/02, B-AT04–07/11/14/17: record exact scope, actual status, failed/partial runs, precision and implementation ancestry | R10–R14 | No |

## 4. Documentation wording

| Change | Exact future files | Reason | Regressions | Frozen theorem changes? |
|---|---|---|---|---|
| Expand the fixed common-embedding bridge | `PROOF.md` §5 or a linked `POVM_BRIDGE.md` | B-E01–B-E06: show the same J for both settings, completion on unused complements, preservation of every joint operator and the bounded/infinite-dimensional argument. Optional defect-projection formula avoids any unproved infinite-dimensional completion assumption | R09 | No |
| Explain the coefficient-ring/actual-embedding distinction | `ROOT_EMBEDDING.md`, `PROOF.md` §§3–4 | FIELD-001/002/008: formal zero is sound without irreducibility; actual root/sign/positivity is separately established. Compatible conjugate embeddings preserve the polynomial identity but need not preserve positive weights | R07–R08 | No |
| Clarify historical annotations and missing historical links | `README.md`, `PROOF.md` §8, `EXACT_KERNELS.json` descriptive `field_relations_file`, `EXACT_SOS_CANDIDATE.json` discovery status | B-S13/B-S14: pointers excluded from the reduced payload are historical, not missing proof premises. Preserve frozen values; label their role in a future wrapper/document | R04, R14 | No |
| Preserve honest scientific limits | `README.md`, future phase summary | No self-testing/uniqueness/all-outcome theorem, no absolute novelty priority, no formal verification or peer review. Numerical searches and audit agreement are not proof by voting | R14 editorial review | No |

## 5. Packaging/replay robustness

- Add a guarded normal-Python entrypoint equivalent to `INDEPENDENT_CHECKS/replay_guard.py`. Reject `-O`, `-OO` and optimization-enabled execution unless every relevant assertion has been replaced by explicit invariant checks. Record optimization flags, source hash, dependencies, argv, cwd and outputs. Files: all future audit runners and `README.md`. Tests: R13–R14. No theorem change.
- Require both process completion and the expected semantic result/residual. A07's exact mutant FAIL with exit 0 must not become PASS in orchestration. Fix the future `c_sos_exact_integer.py` exit contract and driver. Tests: R11/R13. No theorem change.
- Replace hard-coded Windows/sibling paths with explicit `--root`/`--output`; retain adapters separately and hash actual input copies. Files: A06/A07 future replay packaging and `RUN_INSTRUCTIONS.md`. Tests: R01/R14. No theorem change.
- Repair auditor controls themselves: true coordinate negation, actual alternate-root coefficient reevaluation, a genuine abelian quotient versus injected commutator control, correct same-party matrix order, legal five-outcome completeness at d>5, fixed common embedded state, generic tensor-order controls and retained optimizer status/candidate arrays. Exact source paths are in the master ledger. Tests: R07/R09–R13. No theorem change.
- Exclude A07's aborted modular-size bound from proof evidence; its final exact denominator-cleared integer expansion is the replayed route. Do not try to rescue a numerical or modular bound by assuming algebraic residual coordinates are rational integers. Files: future audit errata and `c_size_analysis.py` only if revived. Tests: R06/R14. No theorem change.

## 6. No change / rejected suggestions

- Nonconsecutive block labels 1,6,7,8,9 correctly denote five blocks (B-S15).
- The stated k=0,1 normalization is correct; summing reflected events through k=4 doubles the functional (B-S16).
- A valid broader root enclosure need not be rejected merely because it differs from the frozen narrow box; strict sign proof must still succeed (FIELD-011 and benign controls).
- Cached PASS flags and redundant stored word/interval summaries should remain non-authoritative; recomputation is desirable (B-S09).
- Gram/LDL is useful redundant data-path evidence, but compact SOS plus actual positivity suffices for the upper bound. Neither path authenticates the other's bytes without linkage (FIELD-004/B-S24).
- The standard background Hilbert-space square-root/decomposition interfaces need clear proofs/assumptions, not finite-dimensional restrictions.
- No change to frozen coefficient tables, root polynomial, μ, state amplitudes or measurement phases is supported.

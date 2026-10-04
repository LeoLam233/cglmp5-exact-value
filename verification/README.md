# v0.1.1 acceptance evidence

`release_gate.json` records R01–R14 individually, with hashed receipts and a
binding to the actual release sources. PASS requires the stated semantic
invariants; an exit code alone is never evidence of mathematical success.

## Portable replay

Requirements: normal Python 3, NumPy, SciPy, SymPy and mpmath for the independent
scientific diagnostics. The hardened artifact's five entrypoints need only the
Python standard library. See the relocation receipt for exact tested versions.

Download the immutable Phase-B final-complete release asset, verify SHA-256
`12e2864ed19d99500b72d4aefe6e2b27939fb67c05aa355b38b997456a55fc43`, and extract it
into a new directory called `PHASE_B`. From the repository root, choose fresh
output directories for every run:

```sh
python verification/replay_scientific.py --root . --phase-b PHASE_B --output RUN/scientific
python verification/replay_hardening.py --root . --output RUN/hardening
python verification/test_orchestration.py --root . --output RUN/orchestration
python verification/check_raw_candidates.py --root PHASE_B --output RUN/raw_candidates.json
python verification/check_generic_pvms.py --root . --output RUN/generic_pvms.json
python verification/check_receipt_binding.py --root RUN/hardening --output RUN/receipt_binding.json
python verification/check_relocation.py --root . --output RUN/relocated
python verification/check_integrity.py --root . --archive PHASE_B.zip --source-manifest --output RUN/integrity.json
python scripts/check_release_gate.py
```

The scientific runner copies the Phase-B scripts and inputs byte-for-byte into
the directory layout they require. This is an unchanged-source replay in a new
location, not a claim that old absolute paths are portable by themselves. The
outer adapter takes explicit roots, checks identity of all four scientific JSON
tables against v0.1.1, writes only in its new output tree, records source/input
hashes and inspects precise output statuses and residuals. Original archives and
frozen `artifact_v0.1` are not modified. Historical raw arrays and optimizer
statuses are clearly identified as inputs, not fresh optimization runs.

`check_integrity.py` requires the repository's `v0.1.0` tag to compare all frozen
payload bytes. In a shallow checkout, fetch that tag before running the check.
The root `SHA256SUMS.txt` labels historical v0.1.0 ZIP asset basenames and
current paper/Phase-B external asset basenames; it is not a complete source
manifest. The artifact manifest excludes itself; the release source
manifest excludes itself and mutable receipts/gate. Remote asset hashes are
recorded separately after publication to avoid circular identities.

## Evidence scope

- R06: independent characteristic-zero 273-word compact and 1,681-word Gram
  zero residuals, all 42 LDL and 1,134 E–L coefficients. Finite-field matrix
  checks and normalizer probes are explicitly supplementary diagnostics.
- R07–R08: exact branch signs and independent Fraction signs, all 14 weights
  greater than 1/3000, 100 literal events, 625 Bell entries, 25 eigenvector
  coordinates and 28 saturation vectors (14 R plus 14 adjoints, 700 coordinates).
- R09: exact finite common-embedding and proper-isometry controls plus a
  separately identified analytic review of arbitrary-dimensional interfaces.
- R10–R12: generic ordering and complete five-outcome measurements, intended
  mathematical corruption rejection, exact raw-float feasibility diagnostics
  and strict repaired-representative envelopes. Finite search is not an upper
  bound; repaired strategies differ from their raw floating arrays.
- R02–R05: each actual consumer is tested on files it consumes. The preflight
  consumes all four JSON files; compact/statement consume SOS14; Gram consumes
  the other three. Canonical-format rejection is distinct from mathematical
  falsity. Prose hashes identify bytes, not proof of arbitrary prose.

## Retained failed attempts

`scientific_attempt01` failed one outer receipt expectation: the receipt contains
14 records, each with an R and an adjoint vector. It was incorrectly required to
contain 28 records. The original receipt, runner source and logs remain intact;
`scientific_attempt02` checks all 700 coordinates correctly.

`hardening_attempt01` expected traceback text for rejected mutations. Hardened
entrypoints instead emit structured FAIL JSON with error types. The first
runner's misclassification is preserved; `hardening_attempt02` explicitly
requires SchemaError, CanonicalFormatError or ArithmeticError as appropriate.
These are disclosed regression-runner defects, not rejected scientific tests
silently relabeled PASS.

The deduplicated regression evidence ZIP includes exact file bytes, a full
path-to-hash map and a restoring script. It preserves failed attempts and exact
mutated inputs without repeating thousands of identical source/input copies.
Receipts do not constitute formal verification, human peer review, absolute
novelty clearance, independent-model validation or authenticated unseen history.

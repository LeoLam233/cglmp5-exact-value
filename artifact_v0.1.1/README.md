# CGLMP5 exact certificate, hardened reader v0.1.1

This directory is the additive, non-load-bearing revision of the frozen
[`artifact_v0.1/`](../artifact_v0.1/) payload. The four mathematical JSON files
are byte-identical to that baseline. Coefficients, largest root, attaining
state, measurement phases and arbitrary-local-dimension/five-outcome-POVM
scope are unchanged. The publication manuscript is in [`../paper/`](../paper/).

For the standard CGLMP convention with local bound 2, the exact maximum is the
largest real root of `5 t^6 - 65 t^4 + 144 t^2 + 96 t + 16`, attained on
`C^5 tensor C^5`. The upper bound uses the 14-term positive exact noncommutative
SOS, valid independently of local dimension. Read [PROOF.md](PROOF.md),
[ROOT_EMBEDDING.md](ROOT_EMBEDDING.md), [POVM_BRIDGE.md](POVM_BRIDGE.md), and
[SCHEMA.md](SCHEMA.md). The finite table [SOS14.json](SOS14.json) is part of the
computer-assisted proof object, not a floating-point approximation.

## Reproduce with normal Python

The five current entrypoints require only the Python standard library. From
this directory, writing receipts outside the source package:

```sh
mkdir -p ../current_receipts
python -B validate_integer_encoding.py --root . --output ../current_receipts/encoding.json
python -B verify_sos14.py --root . --output ../current_receipts/compact.json
python -B verify_independent.py --root . --output ../current_receipts/gram.json
python -B verify_statement.py --root . --output ../current_receipts/statement.json
python -B kill_tests.py --root . --output ../current_receipts/kill_tests.json
```

All entrypoints accept explicit `--root` and `--output` paths and do not depend
on a particular OS, sibling workspace, or working directory. Without `--output`
they print their result. `verify_independent.py --skip-physical` emits
`UPPER_BOUND_ONLY_PASS`, never a full-theorem PASS.

Require successful process completion **and the intended semantic status and
checks**. Encoding PASS certifies only schema. Statement PASS checks selected
hard-coded formulas corresponding to the proof, not arbitrary proof prose.
Compact/Gram full PASS includes their reported exact identity, actual positive
embedding and physical attainer checks. `kill_tests.py` must return
`ALL_TESTS_PASSED`. A process exit of zero alone is insufficient evidence.

Every current mathematical reader uses the shared strict decoder and required
schema; the separate preflight is useful but not required for safety. All
optimization-enabled execution (`-O`, `-OO`, nonzero `PYTHONOPTIMIZE`) is refused.
Ordinary caught schema/arithmetic failures write a FAIL result and exit nonzero;
argument/import failures may produce no receipt. Never treat an old output left
behind after failure as a fresh result. The authoritative release regressions
also check altered coefficients and encoding, preserved benign equivalences,
all input/source hashes and semantic outcomes; see [`../verification/`](../verification/).

## What a receipt binds

Each current result includes a versioned receipt naming the actual enforced
theorem, polynomial coefficient order, root selector, scalar basis and eight
standard-event definitions. It hashes actual consumed JSON bytes, current
verifier sources, and available proof/README/schema documents, and records argv,
cwd, interpreter and optimization state. A route does not claim to validate a
file it never reads. Prose hashes bind bytes, not the meaning of modified prose.
Cached status flags, stored interval/word summaries and discovery metadata are
explicitly non-authoritative; see [SCHEMA.md](SCHEMA.md).

`MANIFEST.sha256` is interpreted **relative to this directory**. It excludes
itself and covers the curated package at release; later reproduction outputs
are not silently added. The repository release manifest identifies its own
root separately. Hashes identify bytes, not proof of unseen execution history.

The historical `verification/` tree is copied verbatim from v0.1, including
failed or partial receipts and `packaging_identity.json`. Those reports describe
their original artifacts, paths, times and limited claims. They are not new
v0.1.1 executions and have not been rewritten or retrospectively upgraded.
Frozen Phase-A and Phase-B evidence remains in its historical location/archive.
Current Phase-B errata and source-claim mappings belong to the release evidence,
not to a silently edited original audit.

## Scope and evidence limits

The exact table and explicit analytic bridge support the arbitrary-dimensional
local-five-outcome-POVM theorem. The bridge uses one fixed local embedding J for
both settings, including the unused-complement completion. Formal coefficient
ring identities and positivity in the selected actual embedding are separate
proof obligations; irreducibility is unnecessary for the checked zero identities.

The table's historical `field_relations_file: exact_field.py` names omitted
discovery code, not a missing verifier dependency. The candidate file's old
`POSITIVITY_NOT_YET_CERTIFIED` status is a preserved discovery-stage annotation;
current positivity is recomputed. Earlier novelty-audit pointers in the proof
are historical and do not add proof premises.

The Phase-A/Phase-B AI audit record is supplementary adversarial evidence, with
implementation ancestry, partial failures and exact scope retained. It is not
human peer review or proof by auditor agreement. No claim is made of formal
verification, self-testing, uniqueness, every outcome number, or absolute
novelty/priority. Numerical searches and near-counterexamples are diagnostic,
never a dimension-independent upper-bound proof. Lean work is reserved for a
later milestone and was not performed for this release.

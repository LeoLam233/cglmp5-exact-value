# Pre-completion semantic mutation controls

These are development tests and completion-gate infrastructure, **not** adversarial audits. The validated baseline completion evidence includes their frozen-candidate replay, including source-binding and actual SOS arithmetic corruption. The [current release contract](../../RELEASE_v0.2.0.md) permits release-layer-only changes without another local or remote full clean build or kernel replay while requiring unchanged proof-critical payload and actual lightweight remote release CI on the final commit. Historical development receipts below retain their original scope.

## Executed tests

- `runs/20261004T115337Z/receipt.json`: the original positive baseline and negative executions are retained unchanged. Its claimed `proper_isometry_surjective` PASS is **historical-invalid**: the only diagnostic was stuck typeclass inference, not the intended typed rejection. The receipt also records concurrent source changes and cannot certify a complete frozen suite.
- `runs/20261004T120258Z/receipt.json`: the expanded baseline, three stronger attainment controls and other negative executions are retained unchanged. The same `proper_isometry_surjective` classification is **historical-invalid**. Therefore its overall historical PASS cannot certify that every semantic control passed. The other diagnostics are preserved and satisfy the later strict classifier.
- `source_runs/20261004T115907Z/receipt.json`: five actual production-source mutations. Each original copied source compiled; each mutated copy failed. Every individual source remained unchanged during its own original/mutant pair. Recorded source SHA-256 values distinguish exact originals and mutants. No live production source was changed.

Production mutations cover the modular event shift, order-preserving same-party word reduction, root embedding sign, actual weight sign, and replacing the fixed embedding by a measurement-dependent rotated embedding.

The fixture suite additionally covers compression treated as a homomorphism, a proper isometry treated as surjective, and disappearance of a full-space off-diagonal product-basis coordinate. The attainment lane has added stronger Fourier-offset, normalized-Schmidt, and diagonal-compression counterexample fixtures; the combined `120258Z` fixture replay includes these.

## Historical classification correction

[HISTORICAL_CLASSIFICATION_CORRECTION.json](HISTORICAL_CLASSIFICATION_CORRECTION.json)
records the affected candidate tree, original log/receipt hashes and the exact
[original fixture source](history/proper_isometry_surjective_before_explicit_H.lean.txt).
The old source, logs and claimed outcomes are preserved rather than silently
rewritten. The corrected fixture explicitly supplies `H := ℂ` to the isometry
lemma. A fresh actual typed direction/equality mismatch must be observed in the
clean gate; a synthetic classifier test is not a substitute for that execution.
The production nonsurjectivity/isometry witnesses are unchanged.

The shared `scripts/lean_rejection.py` classifier now requires exit1 and reviewed
proof-failure kinds in the expected file, recording the complete inspected
error diagnostics and raw-log hash. Resource exhaustion, timeouts, parser errors,
missing imports/constants, stuck typeclass inference and other infrastructure
failures are rejected. Fixture coverage is explicit and cannot silently shrink.
The intended proof failure is a control outcome, not an independent inference
of scientific correctness or an adversarial-audit PASS.

## Formal positive witnesses

`CGLMP5.POVMControls` proves:

- `compression_not_multiplicative`
- `commonJ_not_surjective`
- `commonJ_comp_adjoint_ne_one`
- `rotatedCommonJ_isometry`
- `rotatedCommonJ_compression_zero`
- `changing_embedding_changes_effect`

In the last three lemmas both embeddings are valid isometries into the same space, yet compressing the same dilated projection produces different effects. This separates a genuine fixed-embedding requirement from a superficial type mismatch.

`CGLMP5.TensorFinite` identifies every product-basis coordinate of the completed finite tensor product with the full product-index Euclidean space; it does not identify that space with its diagonal subspace.

## Replay

From `repo/lean`, supply the pinned Lake executable:

```
LEAN_NUM_THREADS=1 python ../scripts/limited_build.py python ../scripts/run_lean_negative_controls.py --lake /absolute/path/to/pinned/lake
```

The fixture runner reserves no slot internally, so the outer wrapper reserves one slot for the sequential suite.

For copied production-source mutations:

```
python ../scripts/run_lean_source_mutations.py --lake /absolute/path/to/pinned/lake
```

This second runner acquires a shared slot around each compiler call internally. Do not wrap it in another slot acquisition.

Both runners use isolated temporary copies and leave the live proof sources untouched. Import errors, missing objects, unknown identifiers, timeouts, or a failing original baseline do not count as a successful semantic rejection. Expected-failure fixtures are kept outside the production Lean library.

## Completed SOS mutation gate

The corrupted-certificate-coefficient mutation targets the completed exact SOS/canonical-data dependency path. Its successful execution belongs to the validated baseline completion evidence; earlier development receipts are not relabelled as that result. Source/axiom checks, relocation replay and the completed blind audit round have separate records. Final acceptance follows the preserved-payload contract, with Round 2 cancelled and Round 3 not performed.

## Frozen-candidate output discipline

All three runners accept `--output-dir /absolute/external/directory` and `--require-clean-tree`. For a frozen candidate, both options are required. The directory must be outside the audited repository. The guard checks a clean Git worktree, exact HEAD and tree IDs, and SHA-256 values of every tracked file before and after every compiler check. A change terminates replay and writes `IMMUTABILITY_FAILURE.json`; an existing receipt is marked failed. Python bytecode generation is disabled. Receipts and temporary mutation modules are never written into the audited tree in this mode.

Example frozen fixture replay, after the candidate's whole-tree build:

```
LEAN_NUM_THREADS=1 python ../scripts/limited_build.py python ../scripts/run_lean_negative_controls.py \
  --lake /absolute/path/to/pinned/lake \
  --output-dir /absolute/external/negative-controls \
  --require-clean-tree
```

The same output and cleanliness options apply to `run_lean_source_mutations.py` and `run_lean_source_binding_corruption.py`. The source-mutation runner locks each compiler call internally; the source-binding runner, like the fixture runner, should receive one outer shared-slot wrapper.

Successful checks do not by themselves establish release acceptance. The actual SOS coefficient-corruption execution is separately recorded in the baseline completion evidence; final payload correspondence, lightweight remote release CI and publication remain distinct gates.

## Canonical source-binding corruption

`source_binding_runs/20261004T121223Z/receipt.json` records a genuine changed-numerator test using isolated shadow imports. Both original and mutated data modules compile and pass the exact `RawScalar.valid` predicate, preserving coordinate count and positive denominator. The original source-decode proof passes; after numerator `+1`, the unchanged authentic chunk decode is rejected by kernel evaluation as false. The prior `121111Z` infrastructure attempt, which failed because of module lookup rather than semantics, is preserved and does not count as a passing corruption test.

This checks source binding. It is deliberately distinguished from the later mathematical SOS coefficient-corruption test.

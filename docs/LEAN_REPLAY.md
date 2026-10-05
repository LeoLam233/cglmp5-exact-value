# Pinned Lean replay and CI

## Status and scope

The read-only workflow `.github/workflows/lean-verification.yml` implements the
pinned replay below. Remote execution and acceptance are established only by
commit-bound CI runs and the external receipt bundle; this document is not an
execution receipt. The final roots compiled during development, and the lightweight
readiness inventory check passed. The strict, clean-candidate pipeline and its
fresh-environment kernel replay are separate execution gates. The distinct
actual SOS coefficient-corruption runner has passed a development replay: its original
six-module numeric path passes, the mutated data/lookup/phase path still passes, and
the unchanged residual arithmetic rejects the altered coefficient. Its hook is now
ready; every accepted candidate must rerun it under clean immutable-tree guards.
The local CI-configuration tests have run; they are not a whole-project replay.
No final formalization, adversarial-audit, or release PASS follows from those tests.

A successful run of this workflow is a **completion-gate replay**, not any of the
three mandatory sequential adversarial audit rounds. Release remains blocked until
those rounds pass on the same final Git tree, followed by integrated-commit CI and
remote release verification.

## Immutable inputs

The workflow uses the existing repository-pinned checkout and setup-python action
revisions, an explicitly pinned upload-artifact revision, CPython 3.12 on Linux
x86-64, and these mathematical/toolchain inputs:

- Lean 4.34.1 official Linux archive SHA-256:
  `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`
- mathlib revision: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Exact `lean/lake-manifest.json` SHA-256:
  `96b577b765d936e10a36a561304d42cb13e0a01feec4681ba18c495e03b95116`

`verification/lean/ci/pins.json` records these pins. The sole Python requirement is
a hash-pinned official PyPI zstandard wheel; it reads the pinned runtime archive.
Every runtime regular file and symlink is compared with that archive before replay.
Optimized Python execution is rejected, and subprocesses have inherited
`PYTHONOPTIMIZE` and Lean search/sysroot overrides removed.
All nine dependency repositories are checked out at the exact manifest revisions.
The setup does not run `lake update` or substitute a newer dependency revision.

Only the direct Mathlib imports of the project and their transitive dependency
closure are fetched using pinned mathlib's public `master,legacy` cache readers.
There is no fork-cache fallback, unsafe cache lookup, project-object cache, or
cross-run project-object restoration. Imported proof objects are separately replayed into an empty kernel environment
by the pinned official `leanchecker --fresh CGLMP5`. Ordinary frontend import,
even with `--trust=0`, is not a substitute: a controlled invalid-object fixture
was accepted by that import path and rejected by the official fresh checker.

## Clean relocated replay

Start in a clean, separately checked-out candidate Git tree with its frozen tags
available. Do not copy the development project's `.lake/build` into it. Receipts,
the runtime, and logs must be outside the candidate tree. The commands below assume
CPython 3.12, Git, and network access to the official GitHub/PyPI/mathlib services.

```sh
export PYTHONDONTWRITEBYTECODE=1 LEAN_NUM_THREADS=1
export REPLAY_OUT=/absolute/path/outside/candidate/replay
export RUNTIME_OUT=/absolute/path/outside/candidate/runtime
python -B verification/lean/ci/test_ci_configuration.py
python -B scripts/check_lean_completion_readiness.py \
  --output "$REPLAY_OUT/READINESS.json"
python -m pip install --require-hashes --no-deps \
  -r verification/lean/ci/requirements.txt
python -B scripts/setup_lean_ci.py --work-dir "$RUNTIME_OUT"
export PATH="$RUNTIME_OUT/lean-4.34.1-linux/bin:$PATH"
python -B scripts/run_lean_verification.py \
  --output-dir "$REPLAY_OUT/full" \
  --archive "$RUNTIME_OUT/lean-4.34.1-linux.tar.zst" \
  --runtime "$RUNTIME_OUT/lean-4.34.1-linux"
```

The setup prints the runtime path. On Actions it also writes that path to the
runner-provided environment file for later steps. No credentials are stored.

`run_lean_verification.py` requires a clean Git tree and verifies HEAD, tree hash,
all tracked-file hashes, and worktree cleanliness before and after each stage.
It stops on the first failed stage and preserves the failure receipt and log.
It executes, sequentially:

1. Fail-closed final-root and actual-SOS-mutation readiness checks, then complete
   source-manifest verification in check-only mode. Never run the manifest checker
   with `--write` during frozen replay or audits.
   The source-map coverage guard also requires every mapped declaration and
   documented theorem-family member in the direct inspection inventory, with
   exact source-module linkage.
2. Full runtime readback and fast infrastructure guards, including source-readback
   mutation/optimized-Python/check-only tests, source-manifest controls, and strict SOS
   rejection-classifier controls.
3. Check-only regeneration of the complete source-data family, arithmetic data,
   and staged residual proofs, followed
   by `build_lean_clean.py --clean-project --require-clean-git`: discard only this
   checkout's project build products, topologically compile **every** production
   Lean module, then run plain `lake build`. No production file is excluded merely
   because it is not imported by the umbrella module.
4. Frozen v0.1.1/tag/input validation, reconstruction of generated source fragments,
   and byte-for-byte readback of the actual Lean `CGLMP5.CertificateSource.canonicalSourceBytes` value.
5. Production trust-surface scan, rejecting forbidden proof shortcuts.
6. Final dependency/type/axiom inspection with current-object freshness checks,
   `--fail-if-pending`, and no missing-root fallback. This is metadata inspection,
   not imported-object kernel replay. The receipt preserves every exact printed
   type and axiom set; anything outside `propext`, `Classical.choice`, and
   `Quot.sound` fails the gate.
   The next stage mechanically compares that fresh capture with the exact
   declaration/axiom table in `AXIOM_AUDIT.md`, including module names, literal
   axiom names and universes, and complete inventory coverage.
7. A separate valid/invalid-object control verifies the checker rejects an injected
   kernel type mismatch, followed by genuine fresh-environment kernel replay using
   the official, archive-hash-bound
   `lake env leanchecker --fresh CGLMP5`, after confirming that the umbrella imports
   the complete Main theorem module. Before/after hashes include every available
   project, dependency and runtime object part; changed objects or a nonzero checker
   exit fail. This stage must run alone. Do not call `leanchecker --help` or
   `--version`: those flags are not implemented and can start an unintended scan.
8. Semantic expected-rejection fixtures, genuine production-source mutations,
   canonical-source-decode coefficient corruption, and the separately required
   actual SOS coefficient corruption.

The standalone exact declaration-inspection command, from `lean/`, is:

```sh
LEAN_NUM_THREADS=1 python -B ../verification/lean/inspect_dependencies.py \
  --fail-if-pending \
  --output /absolute/path/outside/candidate/inspection
```

Missing/stale objects, missing required roles, missing scalar multiplication/power
roots, unparsed types or axioms, unexpected axioms, source changes, Lean errors,
and pending declarations all fail. Do not use `--skip-freshness-check` for a final
candidate.

## Resource limits and negative controls

The build orders project modules serially and fixes `LEAN_NUM_THREADS=1`.
Setup, orchestration, and the direct build CLI reject symlinked cache ancestors
or dependency roots and linked production Lean sources before any cache cleanup.
Heavyweight stages use `scripts/limited_build.py`; the source-mutation runner
already locks each compiler itself and must not be wrapped a second time.
The overall runner must not itself be wrapped, because that would nest slot locks.
The CI job runs stages sequentially, allows six hours, and retains failure logs.
Timeout, resource exhaustion, or a dependency download failure is a failed run,
never permission to omit a theorem, reduce the Hilbert-space scope, or accept stale
objects. Public dependency caches reduce disk and CPU needs; they do not replace
the source build or official fresh-environment kernel replay.

Each negative runner accepts `--output-dir EXTERNAL --require-clean-tree`.
Copies or shadow-import directories hold mutations; the candidate source remains
unchanged. A compile failure from missing imports/identifiers is not accepted as
semantic rejection. Both the original and mutant paths must produce the expected
results. Development receipts remain historical evidence and are not relabeled as
immutable final-tree results.

`verification/lean/ci/completion_hooks.json` marks the actual SOS mutation runner
ready after its successful development replay. The runner uses the common `--lake`,
`--output-dir`, and `--require-clean-tree` CLI. It recompiles the unchanged baseline,
then changes one valid Gram numerator and its matching lookup literal together.
All preceding numeric/lookup/phase modules must still pass before the unchanged
actual residual proof rejects the altered arithmetic. Frozen mode additionally
requires the complete SOSIdentity object to be current. The successful development
receipt does not replace that frozen rerun. Deleting pending final-root roles or
omitting the corruption runner cannot turn readiness green.

## Repository access and retained evidence

The workflow has only `contents: read`, disables persisted checkout credentials,
uses no secrets, and contains no push, tag, release, deployment, or publication
step. Its only upload stores verification logs as a normal Actions run artifact.
Outputs live under `RUNNER_TEMP`; no receipt is written into the audited Git tree.
The artifact includes failed readiness and build logs as well as successful
receipts, when available. Archive/toolchain bytes are not redundantly uploaded.

Before accepting a candidate, inspect the semantic outputs and exact axiom sets,
not only process exit codes. A source change invalidates any earlier same-tree
claim and requires replay of affected gates and audits under the mission's repair
rule.

# Finite feature and phase support checks

Development component results, not a final audit or complete theorem replay.
`COMPONENT_STATUS.json` records source and log hashes for every checked module.

Completed:

- 14 literal feature expansions and `SOSExpansionChecks.feature_expansion_checked`.
- All273 normal-word index fibers and `SOSIndexFiberChecks.index_fiber_checked`.
- The zero phase,19 successive phase multiplication steps, all20×20×24 scalar
  phase-pair coordinates, and the `SOSPhaseChecks.phase_pair_check` aggregate.

The original monolithic phase proof exited137. Its exact source and log remain
as `SOSPhaseChecks_attempt01_oom.*`. The same mathematical statement is now
proved in20 fixed-first-phase modules and assembled with kernel-checked
`Fin.cases`; no weakening or external numerical oracle was introduced.
The original first-pass failure list is historical. Its phase failure is resolved
by the checked split architecture.

The first expansion aggregate edit lacked the expected eliminator motive at its
outer application. Its log is retained. The corrected aggregate states the same
universally quantified proposition directly, allowing ordinary `Fin.cases` to
infer the motive. The fiber aggregate uses the same checked assembly pattern.

`scripts/generate_lean_sos_phase_checks.py --check` verifies exact regeneration
of all22 phase source modules without modifying them. This generator only emits
propositions and proof scripts. It does not evaluate a mathematical certificate.

Every fiber was compiled sequentially. Leaves000–083 used one fair ticket each;
subsequent leaves used explicit bounded batches of at most 8 sequential
compiler invocations, with an approximate20-second budget. Batch and per-leaf
exit/log/source-hash receipts are retained. No aggregate build was invoked before
all its leaves had completed.

Actual integer residual closure, the operator identity and final clean replay
are separate gates and are not implied by these support checks alone.

For a new replay, `scripts/build_sos_fiber_batches.py` accepts `--lake` (or resolves Lake on PATH), an inclusive `--start`/`--end` range, and a required external `--output-dir`. It rejects output paths inside the repository, including symlink aliases. `--validate-only` checks these options without invoking a compiler. Existing scientific logs remain unchanged.

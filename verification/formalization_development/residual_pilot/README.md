# Residual kernel-memory development experiments

These are development measurements, not final adversarial audits. Every successful arithmetic identity was checked by `decide +kernel`; external integer arithmetic proposed literals only.

## Observed results on the pre-pure-scalar-split dependency tree

| Experiment | Result | Seconds | Peak RSS KiB |
| --- | --- | ---: | ---: |
| Import SOSIntegerResidualDefinitions only | PASS |8.47|2448604|
| Entire coordinate272,0 by direct kernel reduction | Kernel memory cap failure |7.71|3073540|
| One feature quotient and numerator product, opaque lemmas | PASS |2.28|2604052|
| Explicit63-product integer checksum, NormNum import | PASS |2.07|1635864|
| Same checksum, core-only imports and Int syntax | PASS |0.94|823776|
|24 unique feature stages plus entire coordinate272,0 | PASS |5.37|2586100|
| All24 coordinate stages in one module | Arithmetic stages passed; final Fin-case assembly required repair |72.91|2648368|

The successful staged-coordinate proof makes an opaque theorem identifying the exact literal `fiber272`, rewrites that theorem before simplifying the sum, and separately kernel-checks literal quotient/product values. Direct `simp [fiber]` hit the recursion limit; the explicit lookup theorem removed this table-unfolding problem. The final sum is still a kernel-checked exact integer equality, connected to the original source-defined `integerNumerator`.

The all-coordinate wrapper was repaired using a direct nested `Fin.cases` term with a dependent `Fin.elim0` terminal branch. `SOSResidualSinglePilotAll272.all_coordinates` (namespace `CGLMP5.SOSFinite.All272Pilot`) now builds, and its earlier failed logs remain preserved. During the pure/analytic scalar split, some follow-up checks stopped because a dependency `.olean` was intentionally absent. Those are environment rebuild blockers, not arithmetic failures.

No proof in this directory substitutes a numerical approximation, an externally trusted result, or a finite-field check for the required exact characteristic-zero identity.


## Sparse phase production path

The separate generator `scripts/generate_sos_phase_linear.py` emits 20 small modules containing 480 generic integer-vector identities. Opaque source-table lookup equalities are proved by reflexivity, and each symbolic sparse formula is proved by Lean `norm_num` and `ring`. Every formula has at most four live terms, avoiding repeated evaluation of 60–80 mostlyzero convolution terms after enormous source integers have been substituted. The generated source hashes and counts are in `phase_linear_generation.json`; sequential build receipts are under `phase_linear_builds/`. All 20 phase modules and the aggregate `CGLMP5.SOSPhaseLinear` built successfully. `phase_linear_component_pass.json` records the exact source hashes and 480 checked generic identities. This is a component result, not a final whole-formalization audit.

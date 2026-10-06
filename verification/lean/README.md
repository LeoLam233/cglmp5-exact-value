# Lean declaration dependency/type inspection

This is a development/completion-gate harness. It is not an adversarial audit
and does not by itself establish the scientific theorem. The [current release
contract](../../RELEASE_v0.2.0.md) distinguishes completed baseline evidence,
unchanged proof-critical payload and final-commit remote CI/publication gates;
permitted release-layer changes do not require another local replay or audit.

`declaration_inventory.json` lists the actual final roots, semantic bridge endpoints,
explicitly mapped theorem families, and named model/data definitions. Definition
types and constructors are interfaces, not additional theorem proof roots.
Conditional transfer theorems remain distinguished from instantiated upper bounds
and the actual maximum theorem. The final inspection
fails if any declared root later becomes pending, unavailable or stale.

From `repo/lean`, with the pinned Lean runtime in PATH:

```
LEAN_NUM_THREADS=1 python ../scripts/limited_build.py python ../verification/lean/inspect_dependencies.py \
  --output /absolute/external/development-inspection
```

The script checks Lake freshness without building missing modules. It captures
`#check @declaration` with all quantified binders, universe levels and full names, and exact
`#print axioms declaration` output. It records source and object SHA256 hashes,
source snapshots before/after, tool versions, invocation flags, full raw messages,
parsed axiom sets, missing objects and pending roots. Source mutation during the
run is explicitly recorded. Existing `.olean` presence or a successful default-
trust import is not an independent kernel replay of imported declarations.

## Required final clean-candidate stages

After the candidate has a fresh whole-tree source build, complete the declaration
inventory, ensure there are no pending items, and capture the complete types and
exact axiom sets in the relocated checkout:

```sh
LEAN_NUM_THREADS=1 python ../verification/lean/inspect_dependencies.py \
  --fail-if-pending --output /absolute/path/outside/repository/final-inspection
```

The frontend command records `-DmaxRecDepth=200000 -DmaxHeartbeats=0` before the
input file; these are ordinary resource options, not trust bypasses. Optional
`--trust-zero` adds `--trust=0`, but **does not replay imported proof objects** in
pinned Lean 4.34.1. A controlled external invalid-object fixture demonstrates that
such an object can be imported under that flag and have an empty printed axiom
set. The help text's imported-module claim is not used as evidence.

The separate genuine imported-object gate uses the official tool:

```sh
lake env leanchecker --fresh CGLMP5
```

Run it alone after closure, through the candidate-immutability/receipt wrapper.
The pinned implementation’s global `replayFromFresh` function in `LeanChecker.lean` starts an empty kernel environment and
`Lean.Kernel.Environment.replay` submits the imported and defined declarations to
`Lean.Kernel.Environment.addDeclCore`, checks generated constructors/recursors, and
skips unsafe/partial implementation constants that cannot serve as safe proof
premises. The replay API passes zero heartbeat/recursion limits, documented as
ordinary unlimited resource limits. The independent project trust scan and exact
root axiom allowlist remain mandatory. This is the same official Lean kernel,
not an independently implemented external proof verifier.

Do not invoke `leanchecker --help`: unknown flags are ignored by its pinned CLI
and a targetless invocation begins default project scanning. Consult the pinned
`LeanChecker.lean` source for its interface. Preserve commands, runtime identity,
input source/object hashes, immutable candidate identity, and original/mutant
fixture observations in external receipts. Historical `--trust=0` preflights are
frontend-option checks, not genuine imported-object replays.

The inventory cannot be empty or omit any of the six required final-root roles.
The final gate also requires both `CGLMP5.Scalar.eval_mul` and
`CGLMP5.Scalar.eval_pow` to have been inspected. Missing required roles, invalid
ready entries, pending or unavailable roots, unparsed axiom/type output, a Lean
error, or source mutation during a final run cause nonzero exit. Removing pending
entries from the manifest is not a way to make the gate pass.

The axiom allowlist is exactly `propext`, `Classical.choice`, and `Quot.sound`.
Only displayed universe instantiations are stripped for this comparison; exact
per-declaration names and raw output remain in the receipt. Any other axiom,
including a native-evaluation trust axiom or project-specific axiom, fails every
inspection run. The fast guard tests cover the allowlist and universe parsing.

## Unabridged type output

All printed types use `pp.deepTerms=true`, `pp.proofs=true`, and a raised
`pp.maxSteps` limit. Any remaining Lean omission marker `⋯` fails the harness.
The standard display preserves every quantified binder and assumption while
leaving implicit arguments of applications implicit. Use
`--expand-implicit-arguments` to additionally expand those implementation
arguments; one tensor transfer type alone produces 37 MB in that mode.
The earlier development receipts used Lean's default pretty-printer limits and
contain abbreviated type subexpressions; their exact axiom sets remain valid,
but they are not the final unabridged statement inventory.

The final gate rejects `--skip-freshness-check`; it cannot silently inspect stale
objects as if they were current.

## Mechanically enforced source-map coverage

`mapped_declarations.json` resolves the declaration-like symbolic references in
`SOURCE_MAP.md`, `docs/LEAN_ATTAINMENT_SOURCE_MAP.md`, and
`docs/LEAN_SOS_SOURCE_MAP.md` to exact project module/name pairs. Each ordinary reference has exactly one resolved target. Ambiguous intended
references are explicitly namespace-qualified; competing targets are rejected. Module families,
library APIs, namespace labels and tactics are classified separately. All 480
universally quantified sparse phase-multiplication theorems and all 19 phase-step
theorems are explicitly expanded. Ground source-decoder and residual module
families are represented by their proved complete aggregate interfaces; this is
not a claim that the inventory lists every internal project constant.

`check_mapped_inventory.py` rejects new or stale unclassified symbolic references,
missing/duplicate inventory entries, unresolved recorded targets, changed linked
source hashes, and incomplete theorem families. It is a static coverage check;
actual Lean `#check` in the following inspection resolves every recorded name and
prints its precise type. Final `--fail-if-pending` inspection requires this check
to succeed, even with a separately supplied inventory.

After the fresh inspection, `check_axiom_report.py --inspection
/absolute/external/inspection/inspection.json --output
/absolute/external/AXIOM_REPORT_COMPARISON.json` compares its exact declaration set,
modules, displayed axiom names/universes and complete-type presence against the
tracked inventory and `AXIOM_AUDIT.md` table. It also rejects a stale inventory,
harness or inspected source snapshot. This verifies table consistency without
editing the frozen candidate. It does not infer scientific correctness or replace
the distinct genuine kernel replay. Both consistency guards have synthetic
negative tests, including optimized-Python runs.

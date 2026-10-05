# Main statement integration precheck

Date: 2026-10-04. This is a pre-completion integration check, **not an adversarial
audit round or a formalization-completion verdict**. `Main.lean`, `OperatorTheorem.lean` and the actual SOS dependency graph have now
compiled. Their complete types and exact axiom sets were captured successfully
in `complete_roots_20261004T1400`; the frozen-candidate replay remains separate.

Controlling statements: `paper/main.tex`, Theorem 1 and the immediately preceding
scenario definition; `docs/LEAN_HANDOFF.md`, “One mathematical target.”

## Scope comparison

- `strategy_value_le_mu (S : Strategy.{u,v})` has no certificate, projectivity,
  finite-dimensionality, separability, normality or pure-state premise. Its body
  applies the unconditional `tensor_povm_upper` to all fields of the strategy.
- `Strategy.{u,v}` permits independent local universe levels and arbitrary
  complete complex inner-product spaces. Its measurement fields are exactly
  `Setting → POVM`, with `Setting = Fin 2` and five effects per POVM. A POVM has
  only bounded positive effects and sum equal to identity.
- The bipartite state is an arbitrary normalized positive complex-linear
  functional on all bounded operators of `HTensor Alice Bob`. The tensor space
  is the Hilbert completion of the algebraic complex tensor product. This agrees
  with the manuscript's explicitly permitted normalized-positive-functional
  formulation (paragraph following its probability definition).
- `quantumValues` is the set of actual strategy values, not a set enlarged by
  inserting the desired constant. `mu_mem_quantumValues` uses the explicit
  finite physical attainer and isometric universe transport.
- `quantumValues_isGreatest` supplies both membership and the universal upper
  bound. `quantumValue_exact` separately states the exact supremum equality.
  Both are quantified over each pair of universe levels, without a dimension
  cutoff.
- `cglmp5_exact` packages supremum equality, the literal sextic equation, the
  assertion that every real root is at most `mu`, and the explicit physical
  strategy's value. The universal upper theorem and attained-maximum theorem
  remain separately named roots, rather than hidden assumptions.
- The exact polynomial is `5*t^6 - 65*t^4 + 144*t^2 + 96*t + 16`; the root is the
  actual real `mu` from `Root.lean`, not a quotient-ring symbol or a numerical
  value. Its largest-root property is proved, not assumed in the final roots.
- The literal `cglmp` coefficients retain all eight event families, modular
  shifts, k=0,1, and weights `(2-k)/2`. In particular the asymmetric setting
  pair (1,0) uses the positive shift k+1 and negative shift -k.
  `cglmp_local_bound` and `cglmp_zero_assignment` retain the local bound 2 and
  its attainment as separate exported roots. The final source map should list
  these alongside the `Main.lean` roots.
- `Attainment.explicitStrategy` has both local spaces literally
  `EuclideanSpace ℂ (Fin 5)`. Its state is transported from the full 25-dimensional
  vector into the completed tensor product. `physicalVector_eigen` precedes
  expectation-taking; it is not a claim only about a compressed matrix.
- `commuting_pvm_sos_identity` quantifies over arbitrary bounded PVMs on a
  Hilbert space and assumes only cross-party commutation. Its RHS is the actual
  fourteen-term positive-weight anticommutator sum. No same-party commutation
  or tensor factorization of this representation is imposed.

No type/quantifier weakening was found in this source-level integration check.
The compiled final types now confirm this comparison: no hidden certificate
assumption was introduced during elaboration. This does **not** replace the fresh
whole-tree replay or the required later statement/source adversarial audit.

## Reporting correction

Earlier development inspection receipts used Lean's default pretty-printer
limits. Some highly explicit types therefore contained `⋯`; their exact axiom
sets were unaffected, but those type displays were incomplete. The harness now
prints all quantified binders, universes and full names with depth/proof output
and an increased step limit, and fails on any omission marker. Standard display
leaves application-level implicit arguments implicit. A maximal explicit pilot
for the tensor transfer theorem passed with no omission but produced 37 MB; that
pilot is preserved externally and is not required for ordinary statement review.

The aggregate source role is now ready in development: the revised canonical
whole-file readback passed at 13:26 UTC with all 581335 bytes matching the frozen
SHA256, and all 230 generated source files reproduced unchanged. The eleven
checked header-decoding/physical-gamma bridges are in the inventory. Actual SOS, upper and supremum roots have now compiled and were included in the
complete 141-declaration capture. The frozen-candidate source rerun remains mandatory.

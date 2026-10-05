# Full CGLMP5 attainment source map

This document records the lower-bound dependency lane. It is not a final whole-formalization audit or release verdict.

## Root declarations

- `CGLMP5.Attainment.explicitStrategy : Strategy.{0,0}` uses `EuclideanSpace ℂ (Fin 5)` at both parties, the completed Hilbert tensor product, a normalized positive vector state, and two local five-outcome PVMs per party (converted to POVMs).
- `CGLMP5.Attainment.explicitStrategy_value` proves that its literal `Strategy.value` is the actual selected `mu`.
- `CGLMP5.Attainment.cglmp_attainment` states the same equality directly for the `cglmp` functional and actual `jointProbability` table.
- `CGLMP5.Attainment.physicalVector_eigen` is an eigen-equation in the full completed physical tensor space before taking any expectation.

## Manuscript correspondence

Unqualified attainment declarations below are in `CGLMP5.Attainment`; declarations from `Root.lean` and `TensorFinite.lean` are in `CGLMP5`. Module families denote the checked finite leaf files, not a single declaration. The named aggregate interfaces are included in the [direct type/axiom inventory](../verification/lean/declaration_inventory.json); the accepted candidate must have matching inspection receipts.

The mathematical correspondence is to the frozen v0.1.1 attainment formulas and proof. The current paper also carries approved prior-work/bibliography/PDF maintenance; its attainment and other theorem/proof/data sections are unchanged. [The editorial integration receipt](CURRENT_MAIN_EDITORIAL_INTEGRATION.json) records that distinction. Current whole-paper byte identity to the historical tag is not asserted.

| Published interface | Lean source/declarations |
| --- | --- |
| Actual algebraic embedding and root | `Root.lean`: `mu`, `s`, `u`, `zeta`, `mu_cubic`, `zeta_eq_exp` |
| Alice offsets `(0,1/2)` | `AttainmentFourierFormula.lean`: `alpha_values`, `alice_fourier_formula` |
| Bob offsets `(1/4,-1/4)` and outcome sign `-b` | `AttainmentFourierFormula.lean`: `beta_values`, `bob_fourier_formula` |
| Every Fourier basis orthonormal and complete | `AttainmentOverlap.lean`: `phase_overlap` covers all 100 overlaps; `AttainmentFourier.lean`: `fourier_orthonormal`, `fourierBasis`, `localProjection_positive`, `localProjection_sum`, `localPVM` |
| Exact phases in the actual embedding | `AttainmentPhases.lean`: complete 20-entry table, recurrence, `phase_eq_pow`, `star_phase`, `phase_norm` |
| Manuscript f₁, f₂, f₃, f₄ | `AttainmentAlgebra.lean`: reciprocal-free definitions and `f1_mul_u`, `two_s_mul_f3` |
| Positive a,b and legitimate divisions | `AttainmentAlgebra.lean`: `schmidtDenom_gt_four`, `coeffA_eq_formula`, `coeffB_eq_formula`, `coeffA_pos`, `coeffB_pos` |
| Canonical serialized Schmidt coefficients | `AttainmentSource.lean`: `canonical_gamma`, using the shared exact decoder and `CGLMP5.CertificateSource.gammaRaw` |
| State `(1,a,b,a,1)/sqrt(2+2a²+b²)` | `AttainmentState.lean`: `Attainment.gamma`, `normSq`, `rawState`, `Attainment.state`, `state_apply`, `state_norm` |
| Local projector-to-unitary linkage | `AttainmentMatrixDefs.lean`, `AttainmentSpectral0..3.lean`: 100 exact matrix entries, including relabel shifts and wraparound phases; `AttainmentSpectralLink.lean`: `localSpectral_step`, `alice_unitary_matrix`, `bob_unitary_matrix` |
| Physical local/tensor operator-to-matrix linkage | `AttainmentOperatorLink.lean`: `localProjection_eq_matrix`, `jointProjection_eq_matrix`, `CGLMP5.tensorEuclideanEquiv_operator_kronecker`; `TensorFinite.lean`: `tensorEuclideanEquiv`, `tensorEuclideanEquiv_pure`, `tensorEuclideanEquiv_map_single` |
| Literal published Bell operator | `AttainmentSpectralLink.lean`: `literalBell_coordinates`, relying on the generic `CGLMP5.sosBell_eq_literal` theorem |
| Full-space invariance | `AttainmentBellDefs.lean`: `edgeMatrix_off_diagonal`, `matrixBell_off_diagonal` for every diagonal input and each of 20 off-diagonal output coordinates |
| Exact diagonal Bell entries | `AttainmentColumn0..4.lean`: all 25 diagonal-input/diagonal-output entries of the full matrix |
| Row equations | `AttainmentAlgebra.lean`: `row_zero`, `row_one`, `row_two`; `AttainmentRows.lean`: `toeplitz_gamma` |
| Full 25-dimensional eigen-equation | `AttainmentEigen.lean`: `matrixBell_diagonal_column`, `rawState_mulVec`, `rawState_eigen`, `state_eigen` |
| Physical model attainment | `Attainment.lean`: `physicalVector`, `physicalVector_coordinates`, `physicalVector_norm`, `physicalVector_inner`, `physicalState`, `physicalVector_eigen`, `physicalState_expectation`, `cglmp_attainment`, `explicitStrategy_value` |

## No compressed-only replacement

The finite matrix route proves every full-space output coordinate. Off-diagonal output cancellation follows word by word from actual monomial matrix multiplication; it is not assumed from a compressed Toeplitz eigen-equation. The resulting 25-dimensional operator is connected to the genuine completed tensor product by a full linear isometric equivalence, with each joint local projector transported exactly. This route does not assert that arbitrary compression is multiplicative.

## Exact arithmetic and construction provenance

The physical root of unity is the actual complex exponential, tied to positive square roots in `Root.lean`. Polynomial certificates only use kernel-visible `linear_combination`, ring normalization and explicit scalar relations. Finite residue/shift equalities use kernel decision procedures. No floating value, external SymPy answer, project-specific axiom, `native_decide`, or unproved polynomial identity is a premise.

Historical witness generators and a preserved failed expansion attempt are under `verification/formalization_development/attainment/`. All production Lean sources replay without those generators.

## Source header and verification boundary

`CGLMP5.Attainment.canonical_header_gamma_evaluation` parses the uninterrupted decimal strings rendered by `CGLMP5.CertificateSource.headerLines`, applies the same canonical scalar evaluator, and obtains the five physical Schmidt amplitudes. The public `Attainment` module imports this linkage. The revised whole-source readback is recorded in [the header-aware receipt](../verification/formalization_development/LEAN_SOURCE_BYTES_READBACK_HEADER.json).

Component compilation and source readback are distinct from final artifact acceptance. Independent imported-proof replay uses the pinned official `leanchecker --fresh` route; `--trust=0` by itself is not such a replay. Audit, CI and release acceptance are established only by external receipts identifying the final source tree, under the contract in [the formalization report](../FORMALIZATION_REPORT.md).

# Published-statement / Lean alignment

Status: **the complete proof-source theorem family has passed production builds**. This document records scope alignment and is not an adversarial audit. Baseline completion/replay and one formal blind audit round concern commit `67e0426166c622a63e7daae554560e1ece16a3ba`, tree `c1a5aa737f6bd7f04ea2bc2c22424dd53bcea281`. Final release acceptance requires unchanged proof-critical payload plus final-commit CI and publication receipts under the [current external receipt contract](FORMALIZATION_REPORT.md#external-acceptance-receipt-contract).

Controlling sources: frozen v0.1.1 `docs/LEAN_HANDOFF.md`, `paper/main.tex` (Theorem 1 and Sections 2–6), and `artifact_v0.1.1/`. The freeze/toolchain receipts identify that canonical target. The current `paper/` files also retain approved prior-work/bibliography/PDF maintenance from upstream commit `1e3282749c9fce2163aaeb8415d8936db88d43ad`. Its main-text change is the Acín–Durt–Gisin–Latorre prior-work paragraph; the theorem/proof/data sections are unchanged, as recorded in [the editorial integration receipt](docs/CURRENT_MAIN_EDITORIAL_INTEGRATION.json). Current paper bytes are therefore distinguished from the immutable v0.1.1 manuscript bytes. This document does not change the mathematical target.

## 1. Literal Bell functional and normalization

Published outcomes are 0,…,4 and settings 0,1 at each party. All outcome equalities are modulo 5. The functional has the eight printed event families, summed for k=0,1 with weights 1−k/2.

Lean uses:

- `Outcome := Fin 5`, `Setting := Fin 2`.
- `shifted a b shift` for literal modular equality.
- `eventCoefficientTwo x y a b : Int` for twice the printed coefficient, with all eight families represented before any Fourier transform.
- `cglmp P := ∑ x,y,a,b, (eventCoefficientTwo x y a b : ℝ)/2 * P x y a b`.
- `coefficient_cyclic` identifies the cyclic relabel convention; `asymmetric_event_anchor` guards the shifted `(x,y)=(1,0)` event coefficient.
- `cglmp_local_bound` proves the bound 2 for every convex mixture of deterministic local assignments; `cglmp_zero_assignment` proves attainment of 2. This is the standard finite local polytope definition of a randomized local model.

A final theorem about another Bell coefficient convention, a scaled value, or merely a stored polynomial string would not satisfy the target. `CGLMP5.sosBell_eq_literal` connects the actual sixteen-term SOS Bell operator to the literal coefficient operator after the exact setting 1 outcome relabels.

## 2. Actual largest real root

The published sextic is

`5 μ^6 − 65 μ^4 + 144 μ^2 + 96 μ + 16 = 0`.

`CGLMP5.sextic` in `Root.lean` is the literal polynomial. `mu` is selected by a proved real root existence statement, with `mu_gt_three`, `mu_lt_31_div_10`, and `sextic_mu`. `mu_largest_root` states that every real root of that same polynomial is ≤ mu; `mu_unique_above_three` fixes the relevant branch. Consequently no numerical root approximation, formal quotient-ring root, or unspecified polynomial solution is substituted for the published constant.

The actual embedding also fixes positive `s=√5`, `u=√(10+2s)`, `x=5mu` and the complex `zeta`. `zeta_eq_exp` identifies the physical branch, rather than only a root-of-unity equation.

## 3. Arbitrary local Hilbert spaces and all local POVMs

`Strategy.{u,v}` packages:

- `Alice : Type u` and `Bob : Type v`;
- complex inner product structures, normed additive groups and completeness;
- `State (HTensor Alice Bob)`;
- two settings of five-outcome `POVM` on each local space.

There is no finite-dimensionality, separability, countability, finite-rank, projectivity or purity field. `HTensor H K` is the completion of the algebraic complex tensor product with its Hilbert tensor inner product. It is not the incomplete algebraic tensor product treated as automatically complete.

`POVM H` has five bounded effects, each nonnegative in the bounded-operator order, summing to identity. `jointProbability` applies the state to the actual tensor product of one Alice and one Bob effect. `bellOperator` is the literal finite coefficient sum of those joint operators, and `cglmp_eq_expect_bell` identifies its state expectation with `cglmp`.

Universe-polymorphic universal statements must retain the arbitrary universe parameters. The finite attainer is `Strategy.{0,0}`; `Strategy.lift` and `Strategy.lift_value` transport it into any universe pair without changing its value. The existence of one fixed-dimension witness is solely the lower-bound construction and is not a restriction on the universal upper theorem.

## 4. State scope

The manuscript explicitly permits any normalized positive functional on the bounded-operator algebra, in addition to its introductory density-operator notation. Lean uses that broader permitted functional model as the primitive state definition:

`State H` consists of a positive complex-linear functional on `Op H` with value 1 at identity.

It is not restricted to vector states, finite convex mixtures, density matrices, normal states or separable support. The lower witness is constructed using `State.vector`, but universal statements quantify over the entire `State` type. This document does not claim a separate trace-class/density-operator constructor where none has been supplied; the mechanically stated theorem uses the manuscript's normalized-positive-functional formulation.

## 5. Common-space local POVM bridge

`common_dilation` supplies one setting-independent local embedding into one common dilation space and projectors for both settings. The construction uses proper-isometry defect operators. It does not infer VV*=I from V*V=I.

`dilateState` uses one tensor product of the two fixed local embeddings. `jointProbability_dilate` preserves every `(x,y,a,b)` simultaneously; `cglmp_dilate` preserves the whole literal functional. The local tensor product separation is used at the joint-effect compression step. No arbitrary same-party product is asserted to survive compression multiplicatively.

`povm_bound_of_pvm_bound` and `tensor_povm_bound_of_unitary_bound` are compiled transfer theorems with explicit upper-bound premises. The actual compact certificate is now checked. These generic interfaces retain their explicit premises by design; the unconditional OperatorTheorem and Main instantiations are checked.

The target does not extend to arbitrary abstract commuting POVMs, and no such unproved extension is used.

## 6. Bounded cross-party commuting PVM representation identity

The representation target quantifies over any complex Hilbert space and bounded operators, with local five-outcome PVMs and cross-party commutation. There is no same-party commutation hypothesis.

`PVM` states self-adjointness, outcome orthogonality/idempotence and completeness. `measurementUnitaries` encodes the exactly relabelled outcomes. Fifth-order and unitary properties follow from the spectral calculus; cross-party commutation is preserved. Ordered `Word` semantics retain same-party order.

The checked compact identity has the actual bounded-operator evaluation of

`mu • 1 − B = Σ_j d_j • (R_j*R_j + R_jR_j*)`, with all 14 actual weights strictly positive.

`operator_bound_of_sos` and `state_bound_of_sos` prove the analytic implication for arbitrary bounded representations and all normalized positive states. `commuting_pvm_bound_of_unitary_bound` connects this to literal PVM Bell operators. These are compiled generic implications. The actual `SOS.compact_identity` aggregate has now passed, with every finite coefficient equation and semantic bridge supplied; the [SOS source map](docs/LEAN_SOS_SOURCE_MAP.md) identifies each declaration in that chain. The unconditional OperatorTheorem and Main roots have also passed their production builds.

## 7. Exact physical attainment on C^5⊗C^5

This lane is closed by `CGLMP5.Attainment.explicitStrategy_value`.

Both local spaces in `explicitStrategy` are literally `EuclideanSpace ℂ (Fin 5)`. The local projectors are rank-one projectors onto an orthonormal Fourier basis. The explicit component theorems below are in `CGLMP5.Attainment`:

- `alpha_values`, `alice_fourier_formula`: Alice offsets `(0,1/2)`;
- `beta_values`, `bob_fourier_formula`: Bob offsets `(1/4,−1/4)`, including the negative outcome sign `−b`;
- `localPVM`: self-adjointness, orthogonal products and completeness for all four bases; `localProjection_positive` proves positivity of every effect, and `PVM.toPOVM` supplies the admissible POVMs.

`coeffA_eq_formula`, `coeffB_eq_formula` identify the manuscript amplitudes; their denominator is proved strictly greater than 4, and both amplitudes are positive. `canonical_gamma` links the typed gamma records to these actual physical amplitudes; `canonical_header_gamma_evaluation` further connects uninterrupted source strings emitted by the checked header renderer to the same amplitudes. `state_apply` and `state_norm` give the full normalized vector `(1,a,b,a,1)/sqrt(2+2a²+b²)` in product-basis coordinates.

`localProjection_eq_matrix`, `jointProjection_eq_matrix` and `literalBell_coordinates` establish operator equalities on the full local/tensor spaces. `CGLMP5.tensorEuclideanEquiv` retains every product-basis coordinate, and `CGLMP5.tensorEuclideanEquiv_operator_kronecker` identifies the full tensor operator with its Kronecker matrix. `matrixBell_off_diagonal` proves all 20 off-diagonal output coordinates vanish for every diagonal input. The 25 remaining matrix entries are checked in `AttainmentColumn0..4`; the three independent row equations are exact algebraic identities. `state_eigen` is the full 25-dimensional eigen-equation, and `physicalVector_eigen` transports it to the completed physical tensor product before taking an expectation.

Thus the proved lower witness is not a 5-dimensional compression substituted for C^5⊗C^5. The kernel-checked development controls explicitly construct a full 25-dimensional leakage operator with the same diagonal compression but a different action on the physical state, showing why the weaker compressed equation alone is insufficient.

## 8. Final assembly and acceptance contract

`strategy_value_le_mu` proves, without an outstanding certificate or upper-bound premise,

`∀ S : Strategy.{u,v}, S.value ≤ mu`.

`quantumValue_exact` combines that with the transported `explicitStrategy_value` through `supremum_of_bound_attainment` to conclude

`sSup (quantumValues.{u,v}) = mu`.

The production sources name `commuting_pvm_sos_identity`, `commuting_pvm_upper`, `commuting_pvm_state_upper`, `tensor_povm_upper`, `strategy_value_le_mu`, `quantumValues_isGreatest`, `quantumValue_exact` and `cglmp5_exact`. All these OperatorTheorem and Main statements have passed their production builds. The complete [statement family](SOURCE_MAP.md#handoff-layer-9-and-final-theorem-assembly) also includes the checked local bound/local attainer and the checked physical full-space quantum attainer; it is not reduced to the combined `cglmp5_exact` conclusion.

The validated baseline completion gate is supported by external receipts confirming:

1. the unconditional upper and exact supremum roots are present and whole-tree build succeeds;
2. literal statement/scope comparison is repeated against the frozen manuscript;
3. all final root and load-bearing bridge axiom sets are printed and recorded exactly;
4. no forbidden proof placeholders or project-specific axioms are in the production dependency graph;
5. source binding, exact positivity, same-party word order, common embedding and full-space attainment controls are verified.

One formal blind semantic/source audit round passed on that baseline. Round 2 was cancelled before completion, and Round 3 was not performed. The 6 October 2026 release contract supersedes the earlier three-round requirement and permits non-proof release-layer changes without another local full replay or audit sequence. Final acceptance requires exact proof-critical payload correspondence to the baseline, valid workflow configuration, real remote CI on the final commit and verified publication. The [external receipt contract](FORMALIZATION_REPORT.md#external-acceptance-receipt-contract) distinguishes these scopes; no audit outcome is attributed to changed release-layer bytes.

This alignment document does not establish an audit or release outcome. Those outcomes are established only by the matching external reports and receipts, with the baseline and final release trees identified separately.

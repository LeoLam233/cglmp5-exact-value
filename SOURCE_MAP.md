# CGLMP5 Manuscript and Lean Source Map

## Scope and status of this map

This map links the frozen v0.1.1 mathematical theorem, handoff and exact inputs to the current Lean development. Current paper bytes additionally include approved editorial bibliography/PDF maintenance, as distinguished below. It is integration documentation, not an adversarial audit verdict. The compact identity, every finite aggregate, the unconditional universal upper results and the final maximum/supremum theorem family have passed production builds. Independent replay, audit, CI and release acceptance are established only by the external same-tree receipt contract. See the [development report](FORMALIZATION_REPORT.md), [statement alignment](STATEMENT_ALIGNMENT.md), and [declaration inspection inventory](verification/lean/declaration_inventory.json).

All project code is under `CGLMP5`. Short declaration names below are relative to the namespace declared in their linked source file; the machine-readable inventory records fully qualified names. A file link identifies the actual source; a generic interface with an explicit identity premise must be distinguished from its checked unconditional final instantiation.

## Canonical scientific inputs

| Frozen input | SHA-256 | Role in the selected formal route |
| --- | --- | --- |
| [SOS14.json](artifact_v0.1.1/SOS14.json) | `1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2` | Primary 14-weight, 164-coefficient compact certificate and Schmidt data. Bound to `CertificateSource.canonicalSourceBytes`, decoded to `CertificateSource.rawTerms`, then interpreted by `CanonicalData` and `Scalar.eval`. |
| [EXACT_KERNELS.json](artifact_v0.1.1/EXACT_KERNELS.json) | `6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5` | Frozen auxiliary 81-word/kernel/state reference. The compact route does not take an unchecked kernel table from this file as a premise. Physical amplitudes are linked to the typed gamma records; the dedicated gamma-header text bridge and revised complete-source readback are checked. |
| [EXACT_SOS_CANDIDATE.json](artifact_v0.1.1/EXACT_SOS_CANDIDATE.json) | `14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649` | Frozen auxiliary five-block Gram representation. No completed Lean claim about these auxiliary H matrices is asserted here; they are not needed as premises of the compact 14-term route. |
| [POSITIVITY_CERTIFICATE.json](artifact_v0.1.1/POSITIVITY_CERTIFICATE.json) | `22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de` | Frozen auxiliary LDL/minor-enclosure reference. The adopted proof independently establishes strict positivity of the same compact weights with actual-embedding rational enclosures. No unverified LDL division is assumed. |

The controlling mathematical exposition is `paper/main.tex` at the immutable v0.1.1 tag, and the scope/dependency contract is [docs/LEAN_HANDOFF.md](docs/LEAN_HANDOFF.md). The [current paper source](paper/main.tex) preserves those theorem/proof/data sections while adding the approved Acín–Durt–Gisin–Latorre prior-work paragraph and associated bibliography/PDF maintenance from upstream commit `1e3282749c9fce2163aaeb8415d8936db88d43ad`. The [editorial integration receipt](docs/CURRENT_MAIN_EDITORIAL_INTEGRATION.json) records the current-versus-canonical byte distinction; whole-paper byte identity to the tag is not asserted. [ROOT_EMBEDDING.md](artifact_v0.1.1/ROOT_EMBEDDING.md) distinguishes formal scalar identities from the actual positive embedding and explicitly permits broader proved boxes. [POVM_BRIDGE.md](artifact_v0.1.1/POVM_BRIDGE.md) specifies the fixed-common-space infinite-dimensional interface. [SCHEMA.md](artifact_v0.1.1/SCHEMA.md) fixes the data meaning. These sources guide definitions and statements; descriptive prose and historical PASS flags are not Lean axioms.

All four JSON hashes are preserved in the [freeze receipt](verification/formalization_development/bootstrap/FREEZE_VERIFIED.json). Optional auxiliary Gram/LDL coverage is deliberately distinguished from the load-bearing compact proof, as permitted by the handoff.

## Source decoding into actual numbers

| Source interface | Lean source and declarations | Exact guarantee |
| --- | --- | --- |
| ASCII decimal strings | [CertificateText](lean/CGLMP5/CertificateText.lean): `decimalNatChars`, `decimalNat`, `decimalInt` | Total parsers reject empty digit strings and non-ASCII digits. Integer sign handling is explicit. |
| Bounded source fragments | [CertificateChunks](lean/CGLMP5/CertificateChunks.lean): `DecimalChunks.natural`, `integer`, `text`; `ChunkScalar.decode` | Long strings are split into ordered fragments, with exact base-10 accumulation. Denominator sign handling is separate. |
| Fragment partition semantics | [SourceDecimalSoundness](lean/CGLMP5/SourceDecimalSoundness.lean): `decimalFold_affine`, `DecimalChunks.natural_sound`, `integer_sound`, `ChunkScalar.decode_sound`, `ChunkCoefficient.decode_sound`, `ChunkTerm.decode_sound` | Successful chunk decoding equals uninterrupted text decoding. This is a generic theorem, not a test of selected decimal strings. |
| Typed source records | [CertificateSyntax](lean/CGLMP5/CertificateSyntax.lean): `RawScalar.valid`, `RawCoefficient.valid`, `RawTerm.valid`; [CertificateData](lean/CGLMP5/CertificateData.lean): `rawTerms_valid` | Exactly 24 coordinates and positive denominators; generator labels below 4 and exponents strictly between 0 and 5. |
| Individual source checks | `CertificateChunk00W` through `CertificateChunk13W`, and the corresponding `CertificateChunkXXCYY` modules | All 14 weights and 164 polynomial coefficients decode to their exact typed records. The individual files are imported by the 14 term checks. |
| Complete source object | [CertificateSource](lean/CGLMP5/CertificateSource.lean): `sourceChunkTerms`, `canonicalSourceBytes`, `canonical_source_decode`, `canonical_text_decode` | The 14 complete terms are obtained by both fragment and uninterrupted decimal parsing. This aggregate has passed its development build. |
| Byte identity | [Lean source-value reader](verification/lean/ReadSourceBytes.lean), [revised readback receipt](verification/formalization_development/LEAN_SOURCE_BYTES_READBACK_HEADER.json) | The evaluated Lean string is exactly the 581,335 canonical SOS14 bytes. External SHA-256 readback is paired with the kernel parser theorem; formal SHA-256 is not claimed. |
| Coordinate interpretation | [CanonicalData](lean/CGLMP5/CanonicalData.lean): `decodeScalar`, `CanonicalData.weight`, `CanonicalData.polynomial`, `CanonicalData.gamma`; [ScalarEncoding](lean/CGLMP5/ScalarEncoding.lean): `eval_ofCanonical`, `canonical_denominator_nonzero` | Integer numerators and natural denominators are interpreted without a floating intermediate, in the exact ordered 24-coordinate family. |
| Source word labels | [SourceWordBridge](lean/CGLMP5/SourceWordBridge.lean): `sourceGenerator`, `eval_separateSourceWord`, `rawCoefficient_eval` | Original labels `0,1,2,3` mean the ordered generators `a0,b0,a1,b1`. Separating parties preserves their individual order and uses only cross-party commutation. |
| Canonical Schmidt data | [AttainmentSource](lean/CGLMP5/AttainmentSource.lean): `Attainment.canonical_gamma`; [AttainmentSourceHeader](lean/CGLMP5/AttainmentSourceHeader.lean): `Attainment.canonical_header_gamma_evaluation` | Parsing the uninterrupted strings rendered in the numeric header and applying the shared decoder yields the physical `(1,a,b,a,1)` amplitudes. |

The [header syntax](lean/CGLMP5/CertificateHeaderSyntax.lean), [header data](lean/CGLMP5/CertificateHeaderData.lean) and [header proofs](lean/CGLMP5/CertificateHeaderProofs.lean) now kernel-check the five gamma scalars and all twelve original embedding-box integer strings. `header_gamma_decode` and `header_gamma_text_decode` yield `gammaRaw`; `header_mu_box_decode`, `header_s_box_decode`, `header_u_box_decode` and their `_text_decode` counterparts yield the exact `muBox`, `sBox`, `uBox` records. The renderer `canonicalHeaderPrefix` uses those same checked strings. The source composition uses `headerLines`; the [13:26:20 actual Lean-value readback](verification/formalization_development/LEAN_SOURCE_BYTES_READBACK_HEADER.json) confirms the exact original 581,335 bytes and canonical SHA-256. The validated baseline completion evidence includes source replay; final release requires exact proof-critical payload correspondence. The actual Bell convention, sextic and positive branches are separately defined and proved; they are not inferred from self-descriptive JSON strings.

## Handoff layer 1 and the literal event convention

Manuscript anchors: Section 2, `eq:cglmp`, `eq:relabel`, `eq:cyclic`, Theorem1 local-bound clause.

- [Events](lean/CGLMP5/Events.lean): `Outcome`, `Setting`, `shifted`, `eventCoefficientTwo`, `eventResidue`, `cglmp`.
- `coefficient_deterministic` and `coefficient_cyclic` establish exact coefficient agreement.
- `deterministicTwo_le_four` proves the integer-scaled bound for all 625 assignments; `cglmp_local_bound` extends it to nonnegative normalized local mixtures; `cglmp_zero_assignment` attains 2.
- [BellBridge](lean/CGLMP5/BellBridge.lean): `literalBell`, `cyclicBell`, `sosBell_eq_literal` connect the probability convention to the Fourier/SOS target. Relabelled setting1 outcomes are encoded through `shiftDown` and `measurementUnitaries`.

The cyclic notation is a sum of four experiment expectations. It does not assert a joint distribution for incompatible quantum settings.

## Handoff layers 2 and 3 and actual scalar interpretation

Manuscript anchors: Section 3, `eq:sextic`, `eq:tower`, `eq:cubicmu`, `eq:cubic`, `eq:zeta`, `eq:scalar`, `eq:cyclotomic`.

| Claim | Lean source and declarations |
| --- | --- |
| Actual sextic root exists in `(3,31/10)` | [Root](lean/CGLMP5/Root.lean): `exists_mu`, `mu`, `mu_gt_three`, `mu_lt_31_div_10`, `sextic_mu` |
| The chosen root is the largest real root | `mu_largest_root`, `mu_unique_above_three`, using `sextic_strictMonoOn` |
| Positive radicals and cubic branch | `s_pos`, `s_sq`, `u_pos`, `u_sq`, `mu_cubic`, `x_cubic` |
| Physical complex phase | `sin_pi_div_ten`, `cos_pi_div_ten`, `zeta_eq_exp`, `zeta_primitive` |
| Pure scalar syntax | [ScalarSyntax](lean/CGLMP5/ScalarSyntax.lean): `Scalar`, `ofCanonical`, `Scalar.add`, `neg`, `conj`, `isReal` |
| Actual coordinate evaluation | [ScalarDefs](lean/CGLMP5/ScalarDefs.lean): `basisEval`, `Scalar.eval`, `evalReal`, `eval_add`, `eval_neg`, `eval_conj`, `eval_eq_ofReal` |
| Table-reduction soundness | [ScalarTableData](lean/CGLMP5/ScalarTableData.lean): `mulTerms`; row modules `ScalarTableRow00..23`; [ScalarTable](lean/CGLMP5/ScalarTable.lean): `mulCoeff_sound` |
| Multiplication and power evaluation | [Scalar](lean/CGLMP5/Scalar.lean): `Scalar.eval_mul`; [ScalarConstants](lean/CGLMP5/ScalarConstants.lean): `Scalar.eval_pow`; [ScalarConstantsData](lean/CGLMP5/ScalarConstantsData.lean): `eval_zeta`, `eval_mu` |

Scalar identities are required to evaluate soundly in the actual complex embedding. No assertion that the formal presentation is a field, irreducible or injectively embedded is needed. All 24 rows/576 basis products and the multiplication/power evaluation aggregates have passed their post-split build; see the [durable scalar-engine receipt](verification/formalization_development/scalar_engine_post_split_complete.log) and [bridge freshness receipt](verification/formalization_development/scalar_bridge_freshness.log). Their final frozen-tree type/axiom inspection remains required.

## Handoff layer 4 and ordered noncommutative words

Manuscript anchors: `eq:relations`, Section 4.2 and `eq:wordtest`.

[Words](lean/CGLMP5/Words.lean) proves `PartyWord.eval_reduce`, `PartyWord.eval_adjoint`, `eval_commute`, `Word.evalStar_mul` and `Word.evalStar_adjoint`. The syntax is isolated in [WordSyntax](lean/CGLMP5/WordSyntax.lean). Adjacent equal generators may combine modulo 5; distinct same-party generators remain ordered. Cross-party reordering requires explicit `Commute` hypotheses.

[SOSPolynomial](lean/CGLMP5/SOSPolynomial.lean) proves evaluation of scaling, multiplication, adjoints and anticommutators. `evaluate_eq_of_coefficients` connects a proved finite support/coefficient calculation to representation equality. [SOSGramSemantics](lean/CGLMP5/SOSGramSemantics.lean) and [SOSFeatureSemantics](lean/CGLMP5/SOSFeatureSemantics.lean) justify expansion, factoring, collection and evaluation before they are used for the actual certificate.

## Handoff layer 5 and the compact identity and positivity

Manuscript anchors: Lemma2, `eq:sos`, Sections4.2–4.3. The optional auxiliary Gram presentation is `eq:gramidentity`; it is not an unchecked premise of this route.

| Finite or semantic obligation | Actual source and declaration |
| --- | --- |
| Literal finite Fourier target | [SOSDefinitions](lean/CGLMP5/SOSDefinitions.lean): `fourierCoeff`, `edgeWord`, `edgeCoefficient`, `bell` |
| Actual serialized polynomials | [SOSRealization](lean/CGLMP5/SOSRealization.lean): `SOS.realizingPolynomial` |
| Same source coefficients in phase-compressed form | [SOSCompressedData](lean/CGLMP5/SOSCompressedData.lean): `SOSFinite.core`, `gram`, `phaseTerms`; [SOSCompressedChecks](lean/CGLMP5/SOSCompressedChecks.lean): `gram_pair_checked`, `gram_weight_checked`; [SOSPhaseLink](lean/CGLMP5/SOSPhaseLink.lean): `phasePolynomial_eq_canonical` |
| Exact phase table relations | [SOSPhaseChecks](lean/CGLMP5/SOSPhaseChecks.lean): `SOSFinite.phase_zero`, `phase_step_0..18`, `phase_pair_check` |
| Formal word expansion matches indexed features | [SOSExpansionChecks](lean/CGLMP5/SOSExpansionChecks.lean): `feature_expansion_checked`, with 14 leaf checks |
| Correct collection into every word fiber | [SOSIndexFiberChecks](lean/CGLMP5/SOSIndexFiberChecks.lean): `index_fiber_checked`, with 273 leaf checks |
| Sparse integer phase multiplication | [SOSPhaseLinear](lean/CGLMP5/SOSPhaseLinear.lean) and modules `00..19`: all 480 `phase_linear_e_k` lemmas, each valid for every integer numerator vector; these have all passed |
| Denominator-cleared coordinate semantics | [SOSDenominatorSemantics](lean/CGLMP5/SOSDenominatorSemantics.lean): `Scalar.mul_ofCanonical`, `list_common_denominator`; [SOSIntegerSemantics](lean/CGLMP5/SOSIntegerSemantics.lean): `fiberValue_as_fraction`, `fiberValue_eq_target_of_integer` |
| All actual residuals | [SOSIntegerResidualChecks](lean/CGLMP5/SOSIntegerResidualChecks.lean): `denominator_divides`, `integer_residual`; all 273 production leaves and the aggregate have passed |
| Reflected finite identity implies operator equality | [SOSReflection](lean/CGLMP5/SOSReflection.lean): `reflected_evaluation_eq_target`; the actual residual/reflection aggregate has passed |
| Reflected polynomial is the actual SOS | [SOSSemantics](lean/CGLMP5/SOSSemantics.lean): `reflected_sos_evaluation`; uses exact source/phase/word interfaces |
| Target is exactly `mu*1-B` | [SOSTarget](lean/CGLMP5/SOSTarget.lean): `target_evaluation`, with explicit Fourier coefficient checks; component build passed |
| Final compact identity | [SOSIdentity](lean/CGLMP5/SOSIdentity.lean): `SOS.compact_identity`; actual production aggregate has passed |
| Actual strict positivity | [EmbeddingBounds](lean/CGLMP5/EmbeddingBounds.lean): `ProofBounds.mu_contains`, `s_contains`, `u_contains`, `scalar_enclosure`; [Positivity](lean/CGLMP5/Positivity.lean): `weight_evaluation`, `weight_gt_one_div_three_thousand`, `weight_positive` |

The detailed [compact SOS source map](docs/LEAN_SOS_SOURCE_MAP.md) gives the complete typed-record, finite reflection and actual representation chain through `SOS.compact_identity`, distinguishing the mathematical source records from their decoding and exact-byte provenance gates.

`SOSFinite.gram` denotes weighted core-pair coefficients for the compact route. It must not be confused with an unverified import of the auxiliary H matrices. The counts 4,320 features and 273 normal-word fibers describe the compact expansion; the manuscript's 1,681-word auxiliary Gram universe is a different representation.

## Handoff layers 6 and 7 and arbitrary bounded operators and local POVMs

Manuscript anchors: Sections5.1–5.2, `eq:positiverepresentation`, `eq:fixedJ`, `eq:compression`, `eq:jointcompression`.

| Published analytic interface | Lean source and declarations |
| --- | --- |
| Bounded operators and all normalized positive functionals | [Operator](lean/CGLMP5/Operator.lean): `Op`, `State`, `State.expect`, `operator_bound_of_sos`, `state_bound_of_sos` |
| Finite nonnegative anticommutator sum | `anticommutator_sum_nonneg`, using actual bounded adjoints and positive operator order |
| Proper-isometry defect construction | [POVM](lean/CGLMP5/POVM.lean): `defect`, `defect_comp`, `defect_sq`, `defectUnitary_adjoint`, `defectUnitary_sq` |
| Positive square roots and fivefold Hilbert sum | [POVMConstruction](lean/CGLMP5/POVMConstruction.lean): `POVM.exists_sqrtEffect`, `POVM.analysis`, `DilationAux`, `DilationSpace`, `CGLMP5.commonCoordinatePVM` |
| One local embedding for both settings | [POVMDilation](lean/CGLMP5/POVMDilation.lean): `commonJ`, `commonJ_isometry`, `POVM.dilate_compression`, `common_dilation` |
| Genuine completed Hilbert tensor functor | [Tensor](lean/CGLMP5/Tensor.lean): `HTensor`, `tensorMap`, `tensorMap_comp`, `tensorMap_adjoint`, `tensorMap_isometry`, `tensor_compression` |
| All four setting pairs preserved in one embedded state | [POVMTransfer](lean/CGLMP5/POVMTransfer.lean): `dilateState`, `jointProbability_dilate`, `cglmp_dilate`, `povm_bound_of_pvm_bound` |
| Bounded cross-party commuting PVM upper interface | [OperatorUpper](lean/CGLMP5/OperatorUpper.lean): `commuting_pvm_bound_of_unitary_bound` |
| Tensor-PVM and arbitrary local-POVM transfer | `literalBell_tensor`, `tensor_pvm_bound_of_unitary_bound`, `tensor_povm_bound_of_unitary_bound` |

These generic upper theorems retain an explicit bound/identity premise by design. The checked `OperatorTheorem` instantiations supply the actual compact certificate; the generic interfaces alone are not the unconditional result. No `VV*=1` premise, finite-dimensional completion or compression homomorphism is substituted for the stated construction.

The finite support aggregates [SOSPhaseChecks](lean/CGLMP5/SOSPhaseChecks.lean), [SOSExpansionChecks](lean/CGLMP5/SOSExpansionChecks.lean) and [SOSIndexFiberChecks](lean/CGLMP5/SOSIndexFiberChecks.lean) have all passed: all 20 phase-pair rows,14 term feature expansions and273 normal-word fibers. Their [component receipt](verification/formalization_development/feature_checks/COMPONENT_STATUS.json) records every source/log hash. All 273 production integer-residual leaves have also passed; the actual residual aggregate and compact identity have also passed. The descending219–272 range has a [detailed exit/source-hash receipt](verification/formalization_development/residual_reverse/REVERSE_STATUS.json).

## Handoff layer 8 and full physical attainment

Manuscript anchors: Section 6, `eq:alice`, `eq:bob`, `eq:fs`, `eq:ab`, `eq:state`, `eq:Toeplitz`, `eq:row0..2`.

The detailed [attainment source map](docs/LEAN_ATTAINMENT_SOURCE_MAP.md) is part of this map. Its decisive endpoints are:

- [AttainmentFourierFormula](lean/CGLMP5/AttainmentFourierFormula.lean): `alpha_values`, `beta_values`, `alice_fourier_formula`, `bob_fourier_formula`.
- [AttainmentFourier](lean/CGLMP5/AttainmentFourier.lean): `fourier_orthonormal`, `localProjection_sum`, `localPVM`.
- [AttainmentAlgebra](lean/CGLMP5/AttainmentAlgebra.lean): `schmidtDenom_gt_four`, `coeffA_eq_formula`, `coeffB_eq_formula`, `coeffA_pos`, `coeffB_pos`, the three independent row equations.
- [AttainmentState](lean/CGLMP5/AttainmentState.lean): `Attainment.gamma`, `state_apply`, `state_norm`; the vector has all 25 product-basis coordinates.
- [TensorFinite](lean/CGLMP5/TensorFinite.lean) and [AttainmentOperatorLink](lean/CGLMP5/AttainmentOperatorLink.lean): `tensorEuclideanEquiv`, `tensorEuclideanEquiv_operator_kronecker`, `localProjection_eq_matrix`, `jointProjection_eq_matrix`.
- [AttainmentSpectralLink](lean/CGLMP5/AttainmentSpectralLink.lean): `literalBell_coordinates`.
- [AttainmentBellDefs](lean/CGLMP5/AttainmentBellDefs.lean): `edgeMatrix_off_diagonal`, `matrixBell_off_diagonal`; [AttainmentEigen](lean/CGLMP5/AttainmentEigen.lean): `matrixBell_diagonal_column`, `rawState_eigen`, `state_eigen`.
- [Attainment](lean/CGLMP5/Attainment.lean): `physicalVector_eigen`, `cglmp_attainment`, `explicitStrategy`, `explicitStrategy_value`.

Both local spaces in `explicitStrategy` are exactly `EuclideanSpace ℂ (Fin 5)`. The source-to-PVM, tensor-to-matrix and full-space eigenvector links are operator statements, not compressed expectations.

## Handoff layer 9 and final theorem assembly

[Strategy](lean/CGLMP5/Strategy.lean) defines the universe-polymorphic full model, `Strategy.value`, `quantumValues` and `supremum_of_bound_attainment`. [StrategyTransport](lean/CGLMP5/StrategyTransport.lean) proves transport and universe-lift invariance of the literal value. [LowerValue](lean/CGLMP5/LowerValue.lean) proves `mu_mem_quantumValues`, `quantumValues_nonempty` and `mu_le_every_uniform_bound`.

The final result is a family of mathematical statements, not only one combined exact-value declaration. Every production statement below has passed its compilation gate. Audit and artifact acceptance remain separate receipt-based claims.

| Mathematical role | Exact declaration and source | Current status |
| --- | --- | --- |
| Classical local upper bound | [Events](lean/CGLMP5/Events.lean): `CGLMP5.cglmp_local_bound` | Checked component; arbitrary nonnegative normalized mixtures of all 625 deterministic assignments |
| Classical bound attained | `CGLMP5.cglmp_zero_assignment` | Checked component; literal local value 2 |
| Full physical quantum attainer | [Attainment](lean/CGLMP5/Attainment.lean): `CGLMP5.Attainment.physicalVector_eigen`, `cglmp_attainment`, `explicitStrategy_value` | Checked component; fixed local C^5 spaces and full25-dimensional tensor action |
| Lower witness in every universe pair | [LowerValue](lean/CGLMP5/LowerValue.lean): `CGLMP5.mu_mem_quantumValues` | Checked component; actual strategy transport, no artificial set member |
| Actual compact algebra identity | [SOSIdentity](lean/CGLMP5/SOSIdentity.lean): `CGLMP5.SOS.compact_identity` | Production aggregate checked |
| Arbitrary bounded unitary upper bound | [OperatorTheorem](lean/CGLMP5/OperatorTheorem.lean): `CGLMP5.bounded_unitary_upper` | Production build checked; no finite-dimensional premise |
| Commuting-PVM SOS identity | `CGLMP5.commuting_pvm_sos_identity` | Production build checked; literal Bell operator and actual fourteen weights/polynomials |
| Commuting-PVM operator and state inequalities | `CGLMP5.commuting_pvm_upper`, `CGLMP5.commuting_pvm_state_upper` | Production build checked; arbitrary normalized positive states |
| Original local tensor-product POVM upper bound | `CGLMP5.tensor_povm_upper` | Production build checked; arbitrary local Hilbert universes and completed tensor product |
| All bundled strategy values bounded | [Main](lean/CGLMP5/Main.lean): `CGLMP5.strategy_value_le_mu` | Production build checked |
| Maximum and supremum | `CGLMP5.quantumValues_isGreatest`, `CGLMP5.quantumValue_exact` | Production build checked; independent universes u,v |
| Combined exact value, root characterization and explicit attainment | `CGLMP5.cglmp5_exact` | Production build checked; does not replace the other family members |

The [conditional statement preflight](verification/formalization_development/statement_preflight/README.md) kernel-checks the final assembly with an explicit upper-bound hypothesis. It confirms interface compatibility and is distinct from the subsequently checked unconditional [Main/root build](verification/formalization_development/main_root_build.log). Full types and allowed axiom sets were refreshed for the validated baseline; final release requires exact correspondence of the proof-critical payload and machine-readable inventories under the current receipt contract.

## Verification and nonmathematical provenance

- [Declaration inventory](verification/lean/declaration_inventory.json) and [inspection procedure](verification/lean/README.md): exact type/axiom inspection, including every final theorem-family role and `Scalar.eval_mul`/`Scalar.eval_pow`.
- [Pinned replay instructions](docs/LEAN_REPLAY.md): clean relocated source build, imported-object kernel recheck, source-byte readback and negative controls. The exact declaration table in `AXIOM_AUDIT.md`, baseline replay/audit receipts, final proof-payload comparison and remote CI/publication receipts establish their respective scopes under the current receipt contract; imported-proof replay uses official `leanchecker --fresh`, not `--trust=0` alone.
- [Attainment controls](lean/CGLMP5/AttainmentControls.lean) and [development negative-control receipt](verification/lean_negative_controls/runs/20261004T120258Z/receipt.json): mathematical witnesses and expected rejection of semantic mutations. These are not final audit rounds.
- [Sparse-phase generation record](verification/formalization_development/residual_pilot/phase_linear_generation.json) and [component build receipt](verification/formalization_development/residual_pilot/phase_linear_component_pass.json): source-bound symbolic arithmetic optimization, with all proposed formulas kernel-checked.
- [Development history](verification/formalization_development/): retained memory failures, intermediate diagnostics and successful component receipts. Failed runs are not overwritten as final successes.

The [external receipt contract](FORMALIZATION_REPORT.md#external-acceptance-receipt-contract) governs acceptance: baseline completion and one completed formal blind audit round, unchanged proof-critical payload, valid workflows, real final-commit remote CI, annotated v0.2.0 publication and downloaded-asset verification. Round 2 was cancelled and Round 3 was not performed. The final source tree is recorded separately from the audited baseline; this map does not predeclare pending remote outcomes.

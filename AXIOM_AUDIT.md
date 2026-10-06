# Lean axiom and declaration inspection

Status: **direct exact-type/axiom capture of the final roots, explicitly mapped bridge interfaces and theorem families, and model/data definitions.** Every declaration in the current inspection inventory has compiled and has an unabridged type and exact axiom set recorded below. This report does not claim to list every internal project constant and is not an adversarial audit. Baseline completion and one blind semantic/source audit round are recorded for commit `67e0426166c622a63e7daae554560e1ece16a3ba`, tree `c1a5aa737f6bd7f04ea2bc2c22424dd53bcea281`. Final acceptance follows the [preserved-payload release contract](RELEASE_v0.2.0.md); edits to this report's release prose are not attributed to the baseline audit.

## Procedure and trust boundary

The inventory is `verification/lean/declaration_inventory.json`; the executable harness is `verification/lean/inspect_dependencies.py`. For every ready declaration, the harness checks module freshness with `lake --no-build build`, records source/object hashes, then issues `#check @declaration` and `#print axioms declaration`. It records complete quantified binders, universe levels and full names; deep terms/proofs are enabled, and any omission marker `⋯` fails the run. Application-level implicit instance arguments remain implicit without suppressing quantified hypotheses.

The allowed axiom basenames are exactly `propext`, `Classical.choice`, and `Quot.sound`: propositional extensionality, classical choice and quotient soundness. Displayed universe instantiations are removed only for allowlist comparison; exact returned names remain in the table and raw receipts. Any other axiom causes failure. `decide +kernel` uses kernel reduction, not native proof evaluation.

Types of definitions, abbreviations, structures and constructors are captured to expose the exact model/data interfaces; they are not counted as additional theorem proof roots. Every inventory entry has an explicit declaration kind and an appropriate interface role. The three source maps are linked through `verification/lean/mapped_declarations.json`: every ordinary project-declaration reference has one resolved target, with ambiguous intended references explicitly namespace-qualified. All 480 sparse phase-multiplication theorems and 19 phase-step theorems are directly enumerated. Ground decoder/residual module families retain their proved aggregate interfaces rather than being misrepresented as individually listed helper types.

`check_mapped_inventory.py` enforces that mapped-reference scope before final inspection. `check_axiom_report.py` then compares the newly generated inspection against this exact table and the tracked inventory, rejecting changed names, modules, axiom names/universes, missing types, malformed table rows and stale inventory/harness/source inputs. Both run fail-closed negative tests. These are consistency controls, not scientific-proof oracles.

The capture inspects dependencies of existing current objects and does **not** independently replay their proof bodies. The baseline completion evidence separately establishes the pinned whole-tree source build, official empty-environment kernel replay, semantic/source alignment and required controls. One formal blind Round 1 passed; Round 2 was cancelled and Round 3 was not performed. Final release requires proof-critical byte correspondence and the separate final-commit CI/publication gates, without another local replay or audit sequence for permitted release-layer changes.

## Exact captured axiom sets

The current capture contains 835 declarations: 7 abbrev, 4 constructor, 92 def, 72 lemma, 5 structure, 655 theorem. Lean-source snapshot: `6637e65611e1d67874ba990767b5bb2194af5f2a4557c4271a5938171fdb71f7`. Lean exited 0; sources and inspection inputs were stable; no declarations were pending, unparsed or omitted, and no unexpected axiom was reported. This is development inspection evidence, not the final frozen Git-tree replay receipt.

| Exact returned axiom set | Declaration count |
|---|---:|
| `[]` | 25 |
| `[propext]` | 499 |
| `[propext, Classical.choice.{u}, Quot.sound.{u}]` | 302 |
| `[propext, Quot.sound.{u}]` | 9 |

Every row gives the literal Lean-returned set, including empty sets where appropriate. Full printed types and raw axiom messages are retained in the capture.

| Declaration | Module | Exact axiom set |
|---|---|---|
| `CGLMP5.sextic_mu` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.mu_gt_three` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.mu_largest_root` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.mu_unique_above_three` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.s_sq` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.s_pos` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.u_sq` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.u_pos` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.mu_cubic` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.x_cubic` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.zeta_eq_exp` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.zeta_primitive` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.coefficient_cyclic` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cglmp_local_bound` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cglmp_zero_assignment` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.PartyWord.eval_reduce` | `CGLMP5.Words` | `[propext]` |
| `CGLMP5.PartyWord.eval_adjoint` | `CGLMP5.Words` | `[propext]` |
| `CGLMP5.PartyWord.eval_commute` | `CGLMP5.Words` | `[propext]` |
| `CGLMP5.Word.evalStar_mul` | `CGLMP5.Words` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.Word.evalStar_adjoint` | `CGLMP5.Words` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.eval_separateSourceWord` | `CGLMP5.SourceWordBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.rawCoefficient_eval` | `CGLMP5.SourceWordBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cyclicBell_eq_literal` | `CGLMP5.BellBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.measurementUnitaries_fifth` | `CGLMP5.BellBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.measurementUnitaries_commute` | `CGLMP5.BellBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.sosBell_eq_literal` | `CGLMP5.BellBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.State.expect_le_of_operator_bound` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.anticommutator_sum_nonneg` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.operator_bound_of_sos` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.state_bound_of_sos` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.compression` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.State.pullback` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.State.vector` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensor_ext` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorMap_comp` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorMap_mul` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorMap_cross_commute` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorMap_isometry` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensor_compression` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.commonJ_isometry` | `CGLMP5.POVMDilation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.POVM.dilate_compression` | `CGLMP5.POVMDilation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.common_dilation` | `CGLMP5.POVMDilation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cglmp_eq_expect_bell` | `CGLMP5.POVMTransfer` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.jointProbability_dilate` | `CGLMP5.POVMTransfer` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cglmp_dilate` | `CGLMP5.POVMTransfer` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.povm_bound_of_pvm_bound` | `CGLMP5.POVMTransfer` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.POVM.transport_compression` | `CGLMP5.POVMTransport` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cglmp_transport` | `CGLMP5.POVMTransport` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.commuting_pvm_bound_of_unitary_bound` | `CGLMP5.OperatorUpper` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensor_pvm_bound_of_unitary_bound` | `CGLMP5.OperatorUpper` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensor_povm_bound_of_unitary_bound` | `CGLMP5.OperatorUpper` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Strategy.transport_value` | `CGLMP5.StrategyTransport` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Strategy.lift_value` | `CGLMP5.StrategyTransport` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.supremum_of_bound_attainment` | `CGLMP5.Strategy` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.physicalVector_norm` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.physicalVector_eigen` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.cglmp_attainment` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.explicitStrategy_value` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.exists_attaining_strategy` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.canonical_gamma` | `CGLMP5.AttainmentSource` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.weight_enclosure_lower` | `CGLMP5.Positivity` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.weight_gt_one_div_three_thousand` | `CGLMP5.Positivity` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.weight_positive` | `CGLMP5.Positivity` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.weight_evaluation` | `CGLMP5.Positivity` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.ProofBounds.mu_contains` | `CGLMP5.EmbeddingBounds` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.ProofBounds.s_contains` | `CGLMP5.EmbeddingBounds` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.ProofBounds.u_contains` | `CGLMP5.EmbeddingBounds` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.ProofBounds.scalar_enclosure` | `CGLMP5.EmbeddingBounds` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.DecimalChunks.natural_sound` | `CGLMP5.SourceDecimalSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.DecimalChunks.integer_sound` | `CGLMP5.SourceDecimalSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.ChunkScalar.decode_sound` | `CGLMP5.SourceDecimalSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.ChunkCoefficient.decode_sound` | `CGLMP5.SourceDecimalSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.ChunkTerm.decode_sound` | `CGLMP5.SourceDecimalSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.canonical_denominator_nonzero` | `CGLMP5.ScalarEncoding` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_ofCanonical` | `CGLMP5.ScalarEncoding` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.target_evaluation` | `CGLMP5.SOSTarget` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.mu_mem_quantumValues` | `CGLMP5.LowerValue` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.quantumValues_nonempty` | `CGLMP5.LowerValue` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.mu_le_every_uniform_bound` | `CGLMP5.LowerValue` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.State.mk` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.POVM.mk` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.PVM.mk` | `CGLMP5.Measurements` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Strategy.mk` | `CGLMP5.Strategy` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.compact_identity` | `CGLMP5.SOSIdentity` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.commuting_pvm_sos_identity` | `CGLMP5.OperatorTheorem` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensor_povm_upper` | `CGLMP5.OperatorTheorem` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.canonical_text_decode` | `CGLMP5.CertificateSource` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cglmp5_exact` | `CGLMP5.Main` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.commuting_pvm_upper` | `CGLMP5.OperatorTheorem` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.commuting_pvm_state_upper` | `CGLMP5.OperatorTheorem` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.bounded_unitary_upper` | `CGLMP5.OperatorTheorem` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_mul` | `CGLMP5.Scalar` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_pow` | `CGLMP5.ScalarConstants` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.canonical_source_decode` | `CGLMP5.CertificateSource` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.strategy_value_le_mu` | `CGLMP5.Main` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.quantumValues_isGreatest` | `CGLMP5.Main` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.quantumValue_exact` | `CGLMP5.Main` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.ChunkRational.decode_sound` | `CGLMP5.CertificateHeaderSyntax` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.ChunkBox.decode_sound` | `CGLMP5.CertificateHeaderSyntax` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_gamma_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_gamma_text_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_mu_box_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_mu_box_text_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_s_box_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_s_box_text_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_u_box_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.header_u_box_text_decode` | `CGLMP5.CertificateHeaderProofs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.canonical_header_gamma_evaluation` | `CGLMP5.AttainmentSourceHeader` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_add` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_ofRat` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_conj` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_eq_ofReal` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.mulCoeff_sound` | `CGLMP5.ScalarTable` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_zeta` | `CGLMP5.ScalarConstantsData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_mu` | `CGLMP5.ScalarConstantsData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_mul` | `CGLMP5.SOSPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_adjoint` | `CGLMP5.SOSPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_anticommutator` | `CGLMP5.SOSPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_eq_of_coefficients` | `CGLMP5.SOSPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.eval_sumScalars` | `CGLMP5.SOSScalarPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.coefficient_complexPolynomial` | `CGLMP5.SOSScalarPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.evaluate_indexed` | `CGLMP5.SOSScalarPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.evaluate_indexed_eq` | `CGLMP5.SOSScalarPolynomial` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.mul_ofCanonical` | `CGLMP5.SOSDenominatorSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.common_denominator_term` | `CGLMP5.SOSDenominatorSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.list_common_denominator` | `CGLMP5.SOSDenominatorSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.list_common_denominator_eq` | `CGLMP5.SOSDenominatorSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.featureValue_as_fraction` | `CGLMP5.SOSIntegerSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.fiberValue_as_fraction` | `CGLMP5.SOSIntegerSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.fiberValue_eq_target_of_integer` | `CGLMP5.SOSIntegerSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.integer_residual` | `CGLMP5.SOSIntegerResidualChecks` | `[propext]` |
| `CGLMP5.SOSFinite.denominator_divides` | `CGLMP5.SOSIntegerResidualChecks` | `[propext]` |
| `CGLMP5.SOSFinite.reflected_evaluation_eq_target` | `CGLMP5.SOSReflection` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.reflected_index_coefficients` | `CGLMP5.SOSReflection` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.reflected_sos_evaluation` | `CGLMP5.SOSSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.termReflected_evaluation` | `CGLMP5.SOSSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.gram_evaluation` | `CGLMP5.SOSSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_pair_evaluation` | `CGLMP5.SOSSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.reflected_index_coefficients_of` | `CGLMP5.SOSReflectionCore` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.reflected_evaluation_eq_target_of` | `CGLMP5.SOSReflectionCore` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phasePolynomial_eq_canonical` | `CGLMP5.SOSPhaseLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.rawTerms_valid` | `CGLMP5.CertificateData` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.CanonicalData.rawTerm_valid` | `CGLMP5.CanonicalData` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.CanonicalData.weight_coordinates_length` | `CGLMP5.CanonicalData` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.CanonicalData.weight_denominator_pos` | `CGLMP5.CanonicalData` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.CanonicalData.weight_isReal` | `CGLMP5.CanonicalData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.decimalFold_affine` | `CGLMP5.SourceDecimalSoundness` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.coefficient_deterministic` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.deterministicTwo_le_four` | `CGLMP5.Events` | `[propext]` |
| `CGLMP5.asymmetric_event_anchor` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.eval_neg` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.gramIndex_origin` | `CGLMP5.SOSCompressedData` | `[propext]` |
| `CGLMP5.SOSFinite.gram_pair_checked` | `CGLMP5.SOSCompressedChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.gram_weight_checked` | `CGLMP5.SOSCompressedChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_pair_check` | `CGLMP5.SOSPhaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.feature_expansion_checked` | `CGLMP5.SOSExpansionChecks` | `[propext]` |
| `CGLMP5.SOSFinite.index_fiber_checked` | `CGLMP5.SOSIndexFiberChecks` | `[propext]` |
| `CGLMP5.SOSFinite.gram_as_canonical` | `CGLMP5.SOSIntegerDataSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_as_canonical` | `CGLMP5.SOSIntegerDataSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.target_as_canonical` | `CGLMP5.SOSIntegerDataSoundness` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.target_index_word_map` | `CGLMP5.SOSTargetChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.target_index_coefficients` | `CGLMP5.SOSTargetChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.local_gram_evaluation` | `CGLMP5.SOSSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.term_complex_eq_factored` | `CGLMP5.SOSSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.indexed_feature_coefficient` | `CGLMP5.SOSReflectionCore` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_gramExpand` | `CGLMP5.SOSGramSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_factoredGramExpand` | `CGLMP5.SOSGramSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.coefficient_featurePolynomial` | `CGLMP5.SOSFeatureSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_featurePolynomial_eq` | `CGLMP5.SOSFeatureSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.evaluate_finRange_flatMap` | `CGLMP5.SOSFeatureSemantics` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.defect_comp` | `CGLMP5.POVM` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.adjoint_comp_defect` | `CGLMP5.POVM` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.defect_sq` | `CGLMP5.POVM` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.defectUnitary_adjoint` | `CGLMP5.POVM` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.defectUnitary_sq` | `CGLMP5.POVM` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.POVM.exists_sqrtEffect` | `CGLMP5.POVMConstruction` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.POVM.analysis_isometry` | `CGLMP5.POVMConstruction` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.commonCoordinatePVM` | `CGLMP5.POVMConstruction` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.POVM.analysis_compression` | `CGLMP5.POVMDilation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.POVM.dilationUnitary` | `CGLMP5.POVMDilation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.commonJ` | `CGLMP5.POVMDilation` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorMap_adjoint` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.literalBell_tensor` | `CGLMP5.OperatorUpper` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.alpha_values` | `CGLMP5.AttainmentFourierFormula` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.beta_values` | `CGLMP5.AttainmentFourierFormula` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.alice_fourier_formula` | `CGLMP5.AttainmentFourierFormula` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.bob_fourier_formula` | `CGLMP5.AttainmentFourierFormula` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.fourier_orthonormal` | `CGLMP5.AttainmentFourier` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.localProjection_sum` | `CGLMP5.AttainmentFourier` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.localPVM` | `CGLMP5.AttainmentFourier` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.schmidtDenom_gt_four` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.coeffA_eq_formula` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.coeffB_eq_formula` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.coeffA_pos` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.coeffB_pos` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.row_zero` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.row_one` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.row_two` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.state_apply` | `CGLMP5.AttainmentState` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.state_norm` | `CGLMP5.AttainmentState` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorEuclideanEquiv` | `CGLMP5.TensorFinite` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorEuclideanEquiv_operator_kronecker` | `CGLMP5.AttainmentOperatorLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.localProjection_eq_matrix` | `CGLMP5.AttainmentOperatorLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.jointProjection_eq_matrix` | `CGLMP5.AttainmentOperatorLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.literalBell_coordinates` | `CGLMP5.AttainmentSpectralLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.edgeMatrix_off_diagonal` | `CGLMP5.AttainmentBellDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.matrixBell_off_diagonal` | `CGLMP5.AttainmentBellDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.matrixBell_diagonal_column` | `CGLMP5.AttainmentEigen` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.rawState_mulVec` | `CGLMP5.AttainmentEigen` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.rawState_eigen` | `CGLMP5.AttainmentEigen` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.state_eigen` | `CGLMP5.AttainmentEigen` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.toeplitz_gamma` | `CGLMP5.AttainmentRows` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.gammaRaw` | `CGLMP5.CertificateEmbeddingData` | `[]` |
| `CGLMP5.CertificateSource.headerLines` | `CGLMP5.CertificateHeaderData` | `[propext]` |
| `CGLMP5.CanonicalData.polynomial` | `CGLMP5.CanonicalData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CanonicalData.rawTerm` | `CGLMP5.CanonicalData` | `[]` |
| `CGLMP5.CanonicalData.weight` | `CGLMP5.CanonicalData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.canonicalSourceBytes` | `CGLMP5.CertificateSource` | `[propext]` |
| `CGLMP5.CertificateSource.rawTerms` | `CGLMP5.CertificateData` | `[]` |
| `CGLMP5.CertificateSource.ChunkScalar.decode` | `CGLMP5.CertificateChunks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.DecimalChunks.natural` | `CGLMP5.CertificateChunks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.DilationAux` | `CGLMP5.POVMConstruction` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.DilationSpace` | `CGLMP5.POVMConstruction` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.HTensor` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Op` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Outcome` | `CGLMP5.Events` | `[]` |
| `CGLMP5.POVM.analysis` | `CGLMP5.POVMConstruction` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.PartyWord.push` | `CGLMP5.WordSyntax` | `[]` |
| `CGLMP5.PartyWord.reduce` | `CGLMP5.WordSyntax` | `[]` |
| `CGLMP5.CertificateSource.RawCoefficient.valid` | `CGLMP5.CertificateSyntax` | `[]` |
| `CGLMP5.CertificateSource.RawScalar.valid` | `CGLMP5.CertificateSyntax` | `[]` |
| `CGLMP5.CertificateSource.RawTerm.valid` | `CGLMP5.CertificateSyntax` | `[]` |
| `CGLMP5.SOS.realizingPolynomial` | `CGLMP5.SOSRealization` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.gram` | `CGLMP5.SOSCompressedData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar` | `CGLMP5.ScalarSyntax` | `[]` |
| `CGLMP5.Scalar.eval` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Setting` | `CGLMP5.Events` | `[]` |
| `CGLMP5.State` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.State.expect` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Strategy.value` | `CGLMP5.Strategy` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Word.evalStar` | `CGLMP5.Words` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.QInterval.add` | `CGLMP5.ScalarIntervals` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.add` | `CGLMP5.ScalarSyntax` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.basisEval` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.bell` | `CGLMP5.SOSDefinitions` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.canonicalHeaderPrefix` | `CGLMP5.CertificateHeaderData` | `[propext]` |
| `CGLMP5.cglmp` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.conj` | `CGLMP5.ScalarSyntax` | `[]` |
| `CGLMP5.SOSFinite.core` | `CGLMP5.SOSCompressedData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cos_pi_div_ten` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.cyclicBell` | `CGLMP5.BellBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.decimalInt` | `CGLMP5.CertificateText` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.decimalNat` | `CGLMP5.CertificateText` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.decimalNatChars` | `CGLMP5.CertificateText` | `[]` |
| `CGLMP5.CanonicalData.decodeScalar` | `CGLMP5.CanonicalData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.defect` | `CGLMP5.POVM` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.dilateState` | `CGLMP5.POVMTransfer` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.edgeCoefficient` | `CGLMP5.SOSDefinitions` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.edgeWord` | `CGLMP5.SOSDefinitions` | `[propext]` |
| `CGLMP5.PVM.eval` | `CGLMP5.Spectral` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.PartyWord.eval` | `CGLMP5.Words` | `[]` |
| `CGLMP5.Word.eval` | `CGLMP5.Words` | `[]` |
| `CGLMP5.Scalar.evalReal` | `CGLMP5.ScalarDefs` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Word.eval_adjoint` | `CGLMP5.Words` | `[propext]` |
| `CGLMP5.PVM.eval_mul` | `CGLMP5.Spectral` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Word.eval_mul` | `CGLMP5.Words` | `[propext]` |
| `CGLMP5.PVM.eval_pow` | `CGLMP5.Spectral` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.eventCoefficientTwo` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.eventResidue` | `CGLMP5.Events` | `[]` |
| `CGLMP5.exists_mu` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.explicitStrategy` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.f1_mul_u` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.fourierBasis` | `CGLMP5.AttainmentFourier` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOS.fourierCoeff` | `CGLMP5.SOSDefinitions` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.gamma` | `CGLMP5.AttainmentState` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CanonicalData.gamma` | `CGLMP5.CanonicalData` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.DecimalChunks.integer` | `CGLMP5.CertificateChunks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.isReal` | `CGLMP5.ScalarSyntax` | `[propext, Quot.sound.{u}]` |
| `CGLMP5.jointProbability` | `CGLMP5.POVMTransfer` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.literalBell` | `CGLMP5.BellBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.measurementUnitaries` | `CGLMP5.BellBridge` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.mu` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.muBox` | `CGLMP5.CertificateEmbeddingData` | `[]` |
| `CGLMP5.mu_lt_31_div_10` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.mulTerms` | `CGLMP5.ScalarTableData` | `[propext]` |
| `CGLMP5.Scalar.neg` | `CGLMP5.ScalarSyntax` | `[]` |
| `CGLMP5.Attainment.normSq` | `CGLMP5.AttainmentState` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Scalar.ofCanonical` | `CGLMP5.ScalarSyntax` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phaseTerms` | `CGLMP5.SOSCompressedData` | `[propext]` |
| `CGLMP5.Attainment.phase_eq_pow` | `CGLMP5.AttainmentPhases` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_linear_0_0` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_1` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_10` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_11` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_12` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_13` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_14` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_15` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_16` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_17` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_18` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_19` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_2` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_20` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_21` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_22` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_23` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_3` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_4` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_5` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_6` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_7` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_8` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_0_9` | `CGLMP5.SOSPhaseLinear00` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_0` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_1` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_10` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_11` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_12` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_13` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_14` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_15` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_16` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_17` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_18` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_19` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_2` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_20` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_21` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_22` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_23` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_3` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_4` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_5` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_6` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_7` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_8` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_10_9` | `CGLMP5.SOSPhaseLinear10` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_0` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_1` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_10` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_11` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_12` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_13` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_14` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_15` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_16` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_17` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_18` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_19` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_2` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_20` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_21` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_22` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_23` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_3` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_4` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_5` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_6` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_7` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_8` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_11_9` | `CGLMP5.SOSPhaseLinear11` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_0` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_1` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_10` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_11` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_12` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_13` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_14` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_15` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_16` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_17` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_18` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_19` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_2` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_20` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_21` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_22` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_23` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_3` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_4` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_5` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_6` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_7` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_8` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_12_9` | `CGLMP5.SOSPhaseLinear12` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_0` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_1` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_10` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_11` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_12` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_13` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_14` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_15` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_16` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_17` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_18` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_19` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_2` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_20` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_21` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_22` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_23` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_3` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_4` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_5` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_6` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_7` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_8` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_13_9` | `CGLMP5.SOSPhaseLinear13` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_0` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_1` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_10` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_11` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_12` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_13` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_14` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_15` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_16` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_17` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_18` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_19` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_2` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_20` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_21` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_22` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_23` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_3` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_4` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_5` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_6` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_7` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_8` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_14_9` | `CGLMP5.SOSPhaseLinear14` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_0` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_1` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_10` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_11` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_12` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_13` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_14` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_15` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_16` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_17` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_18` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_19` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_2` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_20` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_21` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_22` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_23` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_3` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_4` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_5` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_6` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_7` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_8` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_15_9` | `CGLMP5.SOSPhaseLinear15` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_0` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_1` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_10` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_11` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_12` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_13` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_14` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_15` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_16` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_17` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_18` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_19` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_2` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_20` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_21` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_22` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_23` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_3` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_4` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_5` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_6` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_7` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_8` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_16_9` | `CGLMP5.SOSPhaseLinear16` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_0` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_1` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_10` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_11` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_12` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_13` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_14` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_15` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_16` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_17` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_18` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_19` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_2` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_20` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_21` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_22` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_23` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_3` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_4` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_5` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_6` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_7` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_8` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_17_9` | `CGLMP5.SOSPhaseLinear17` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_0` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_1` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_10` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_11` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_12` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_13` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_14` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_15` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_16` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_17` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_18` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_19` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_2` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_20` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_21` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_22` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_23` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_3` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_4` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_5` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_6` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_7` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_8` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_18_9` | `CGLMP5.SOSPhaseLinear18` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_0` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_1` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_10` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_11` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_12` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_13` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_14` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_15` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_16` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_17` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_18` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_19` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_2` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_20` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_21` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_22` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_23` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_3` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_4` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_5` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_6` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_7` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_8` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_19_9` | `CGLMP5.SOSPhaseLinear19` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_0` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_1` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_10` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_11` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_12` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_13` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_14` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_15` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_16` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_17` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_18` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_19` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_2` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_20` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_21` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_22` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_23` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_3` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_4` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_5` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_6` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_7` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_8` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_1_9` | `CGLMP5.SOSPhaseLinear01` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_0` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_1` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_10` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_11` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_12` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_13` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_14` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_15` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_16` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_17` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_18` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_19` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_2` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_20` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_21` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_22` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_23` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_3` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_4` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_5` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_6` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_7` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_8` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_2_9` | `CGLMP5.SOSPhaseLinear02` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_0` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_1` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_10` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_11` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_12` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_13` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_14` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_15` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_16` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_17` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_18` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_19` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_2` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_20` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_21` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_22` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_23` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_3` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_4` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_5` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_6` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_7` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_8` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_3_9` | `CGLMP5.SOSPhaseLinear03` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_0` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_1` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_10` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_11` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_12` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_13` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_14` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_15` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_16` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_17` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_18` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_19` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_2` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_20` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_21` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_22` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_23` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_3` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_4` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_5` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_6` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_7` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_8` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_4_9` | `CGLMP5.SOSPhaseLinear04` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_0` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_1` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_10` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_11` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_12` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_13` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_14` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_15` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_16` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_17` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_18` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_19` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_2` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_20` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_21` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_22` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_23` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_3` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_4` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_5` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_6` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_7` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_8` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_5_9` | `CGLMP5.SOSPhaseLinear05` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_0` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_1` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_10` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_11` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_12` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_13` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_14` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_15` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_16` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_17` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_18` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_19` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_2` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_20` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_21` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_22` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_23` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_3` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_4` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_5` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_6` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_7` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_8` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_6_9` | `CGLMP5.SOSPhaseLinear06` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_0` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_1` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_10` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_11` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_12` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_13` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_14` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_15` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_16` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_17` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_18` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_19` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_2` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_20` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_21` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_22` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_23` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_3` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_4` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_5` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_6` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_7` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_8` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_7_9` | `CGLMP5.SOSPhaseLinear07` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_0` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_1` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_10` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_11` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_12` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_13` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_14` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_15` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_16` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_17` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_18` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_19` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_2` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_20` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_21` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_22` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_23` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_3` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_4` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_5` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_6` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_7` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_8` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_8_9` | `CGLMP5.SOSPhaseLinear08` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_0` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_1` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_10` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_11` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_12` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_13` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_14` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_15` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_16` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_17` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_18` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_19` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_2` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_20` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_21` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_22` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_23` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_3` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_4` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_5` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_6` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_7` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_8` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.SOSFinite.phase_linear_9_9` | `CGLMP5.SOSPhaseLinear09` | `[propext]` |
| `CGLMP5.Attainment.phase_norm` | `CGLMP5.AttainmentPhases` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_0` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_1` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_2` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_3` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_4` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_5` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_6` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_7` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_8` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_9` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_10` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_11` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_12` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_13` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_14` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_15` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_16` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_17` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_step_18` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.phase_zero` | `CGLMP5.AttainmentPhases` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.SOSFinite.phase_zero` | `CGLMP5.SOSPhaseBaseChecks` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.physicalState` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.physicalVector` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.quantumValues` | `CGLMP5.Strategy` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.rawState` | `CGLMP5.AttainmentState` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.s` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.sBox` | `CGLMP5.CertificateEmbeddingData` | `[]` |
| `CGLMP5.sextic_strictMonoOn` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.shiftDown` | `CGLMP5.Fourier` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.shifted` | `CGLMP5.Events` | `[]` |
| `CGLMP5.sin_pi_div_ten` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.sourceChunkTerms` | `CGLMP5.CertificateSource` | `[]` |
| `CGLMP5.CertificateSource.sourceGenerator` | `CGLMP5.SourceWordBridge` | `[propext]` |
| `CGLMP5.Attainment.star_phase` | `CGLMP5.AttainmentPhases` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.state` | `CGLMP5.AttainmentState` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorMap` | `CGLMP5.Tensor` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.DecimalChunks.text` | `CGLMP5.CertificateChunks` | `[propext]` |
| `CGLMP5.Attainment.two_s_mul_f3` | `CGLMP5.AttainmentAlgebra` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.u` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.uBox` | `CGLMP5.CertificateEmbeddingData` | `[]` |
| `CGLMP5.zeta` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.physicalVector_coordinates` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.physicalVector_inner` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorEuclideanEquiv_pure` | `CGLMP5.TensorFinite` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.tensorEuclideanEquiv_map_single` | `CGLMP5.TensorFinite` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.deterministicBehavior` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.localBehavior` | `CGLMP5.Events` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Strategy.transport` | `CGLMP5.StrategyTransport` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Strategy.lift` | `CGLMP5.StrategyTransport` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.CertificateSource.rawTerms_length` | `CGLMP5.CertificateData` | `[]` |
| `CGLMP5.SOSFinite.all_denominators_positive` | `CGLMP5.SOSIntegerData` | `[]` |
| `CGLMP5.POVM` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.PVM` | `CGLMP5.Measurements` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Strategy` | `CGLMP5.Strategy` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Word` | `CGLMP5.WordSyntax` | `[]` |
| `CGLMP5.bellOperator` | `CGLMP5.POVMTransfer` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.sextic` | `CGLMP5.Root` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.alice_unitary_matrix` | `CGLMP5.AttainmentSpectralLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.bob_unitary_matrix` | `CGLMP5.AttainmentSpectralLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.localProjection_positive` | `CGLMP5.AttainmentFourier` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.localSpectral_step` | `CGLMP5.AttainmentSpectralLink` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.phase_overlap` | `CGLMP5.AttainmentOverlap` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.Attainment.physicalState_expectation` | `CGLMP5.Attainment` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |
| `CGLMP5.PVM.toPOVM` | `CGLMP5.Operator` | `[propext, Classical.choice.{u}, Quot.sound.{u}]` |

## Actual final-root coverage

The complete capture includes the actual compact identity `SOS.compact_identity`; the unconditional bounded-unitary, commuting-PVM operator/state and tensor-POVM upper bounds; `strategy_value_le_mu`; `quantumValues_isGreatest`; `quantumValue_exact`; and `cglmp5_exact`. None has a pending certificate premise. The generic conditional transfer lemmas remain separately labelled interfaces in the machine-readable inventory.

The printed `Strategy.{u,v}` and tensor-POVM root retain independent local universe levels and only the complete complex Hilbert-space structures, arbitrary five-outcome local POVMs and normalized positive state. The compact representation root assumes only the intended star-algebra structure, unitary generators, fifth-order relations and cross-party commutation. The exact-value root combines the actual supremum, literal sextic, largest-real-root property and physical finite-dimensional attainer.

The aggregate source interfaces are directly captured: canonical term source/text decoders, generic decimal chunk soundness, gamma/box header decoders, and actual physical gamma evaluation. Ground decoder and residual leaves are kernel-checked and represented in this direct inventory by their complete aggregate theorems; every such leaf is still included in the whole-production build and genuine kernel replay. The revised actual Lean rendering reproduced all 581335 canonical bytes with SHA256 `1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2`; regeneration left all 230 generated source files unchanged. The frozen-candidate source-binding receipt remains a separate mandatory acceptance condition.

## Preserved development evidence

The expanded [835-declaration inspection receipt](verification/formalization_development/dependency_inspection/final_mapped_20261004T1651/inspection.json), [complete types and exact axiom output](verification/formalization_development/dependency_inspection/final_mapped_20261004T1651/TYPES_AND_AXIOMS.txt), and [raw Lean messages](verification/formalization_development/dependency_inspection/final_mapped_20261004T1651/lean_output.jsonl) record the actual sets in this table. They include mapped-reference coverage, source/object hashes, tool identity and unchanged inspection-input hashes. The baseline completion replay regenerated and mechanically compared this evidence; the development capture is not reused as that execution result. The table remains unchanged by the release-contract prose update.

The historical [complete-root inspection receipt](verification/formalization_development/dependency_inspection/complete_roots_20261004T1400/inspection.json), [complete printed types and exact axiom output](verification/formalization_development/dependency_inspection/complete_roots_20261004T1400/TYPES_AND_AXIOMS.txt), and [raw Lean messages](verification/formalization_development/dependency_inspection/complete_roots_20261004T1400/lean_output.jsonl) are included with the source. That earlier capture records all 141 then-listed declarations and their development snapshot, invocation and object hashes. Its exact sets remain valid historical evidence, but its direct bridge coverage was incomplete: it omitted some mapped Fourier, full-space, proper-isometry, finite-reflection and scalar-family interfaces. The expanded inventory supersedes it for completion-gate coverage. Neither historical capture substitutes for final frozen-tree acceptance receipts.

Earlier retained development evidence includes the 98-declaration full-type capture, the 24-declaration interpretation-bridge supplement, their 120-declaration union, a successful 37 MB maximal-explicit type pilot, and the first failed harness attempt caused by an unsupported `pp.width` option. The older 76- and 85-declaration captures had valid exact axiom outputs but abbreviated pretty-printed types; those displays are superseded by the complete-root capture. These historical attempts remain preserved in the development evidence archive and are not relabelled as final passing replays.

The previous harness source is preserved as `verification/formalization_development/dependency_inspection/inspect_dependencies_before_full_types.py.txt`. Acceptance receipts produced after source freeze are governed by the [external acceptance receipt contract](FORMALIZATION_REPORT.md#external-acceptance-receipt-contract), rather than by unpublished local paths.

## Reproducing frozen-candidate inspection

The following procedure describes the baseline completion check and independent reproduction. It does not require an additional local replay for this release's permitted release-layer edits. After every final root is compiled, its exact type/set is recorded, the inventory has no pending role, and a fresh whole-tree source build succeeds, freeze the candidate. Run the following **alone** in the clean relocated checkout, with outputs outside its Git tree:

```sh
cd lean
LEAN_NUM_THREADS=1 python ../verification/lean/inspect_dependencies.py \
  --fail-if-pending \
  --output /absolute/external/receipt-directory
```

Type/axiom inspection and genuine imported-object replay are separate stages. The frontend command includes ordinary `-DmaxRecDepth=200000 -DmaxHeartbeats=0` resource options before imports. Pinned Lean 4.34.1 accepts a deliberately invalid external theorem object even under `--trust=0`; that flag does not establish imported-proof validity despite its help text. The separate official `lake env leanchecker --fresh CGLMP5` stage starts an empty kernel environment and re-adds declarations via `Lean.Kernel.Environment.addDeclCore`, including constructor/recursor checks. Its replay API uses ordinary unlimited heartbeat/recursion limits (0,0). Unsafe/partial implementation constants are excluded by the official replayer and cannot be safe proof premises; the project forbidden-token scan and exact root axiom allowlist are independently required. This is a fresh replay through the official kernel, not a separately implemented proof verifier. The harness fails for pending/unavailable roots, unexpected axioms, unparsed or omitted types, source mutation, or a failed Lean invocation. Final mode forbids bypassing module freshness. The required scalar evaluation roots and all six final-role categories must be present.

Keep the imported-object replay receipt, exact invocation, complete type/axiom outputs, and source/object hashes external to the tree they describe. Baseline audit and completion receipts retain their original identities. The current release contract permits changes to release prose and infrastructure only with an explicit final payload comparison; any proof-critical change fails that correspondence gate and cannot inherit the baseline result.

Imported-object replay and adversarial-audit acceptance are determined by their external receipts for the frozen tree, not by editing this declaration report after the fact. The earlier `--trust=0` syntax preflight is retained only as an option/integration check; it is not imported-proof validity evidence. The historical [controlled valid/invalid-object comparison](verification/formalization_development/checker_fixture/CONCLUSION.json) records that ordinary trust-zero imports accept the invalid object, whereas both official module replay and `--fresh` replay reject it with the [kernel declaration-type-mismatch diagnostic](verification/formalization_development/checker_fixture/checker_fresh_InvalidObject.log); the valid counterpart passes. The [reproducible fixture runner](scripts/run_lean_checker_fixture.py) also forms part of the completed baseline gate and the documented remote replay procedure.

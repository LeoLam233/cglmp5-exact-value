# CGLMP5 Lean Formalization Report

## Current conclusion

The full published CGLMP5 theorem family is implemented and has passed production Lean builds: the local bound 2 with an attainer, the actual compact SOS identity, the arbitrary bounded commuting-PVM identity, the unrestricted local tensor-product POVM upper bound, full `C^5 ⊗ C^5` attainment, and the exact largest-sextic-root quantum maximum.

These are proof-source and component-build results, recorded on 4 October 2026. Independent kernel replay, adversarial acceptance, CI and publication are established only by the same-tree external receipts specified below. This document is not its own audit or release verdict. Merely finding a declaration in a source file is not evidence that it was checked.

The controlling mathematical target remains the remotely verified annotated v0.1.1 release. The [statement alignment](STATEMENT_ALIGNMENT.md) records the quantifiers and exclusions. The [source map](SOURCE_MAP.md) links the full theorem family, manuscript and canonical data to exact declarations. The [declaration inventory](verification/lean/declaration_inventory.json) lists final roots, mapped load-bearing bridges and construction interfaces, distinguishing definitions from theorem roots. Exact types and axiom sets must be bound to the accepted candidate's inspection receipts; a name-coverage check alone does not establish their inspected contents.

## Fixed mathematical target

The required result is the standard five-outcome CGLMP maximum, with local bound 2:

`sup I5 = mu`, where `mu` is the largest real root of `5*mu^6 - 65*mu^4 + 144*mu^2 + 96*mu + 16 = 0`.

The upper conclusion quantifies over arbitrary complex local Hilbert spaces, arbitrary five-outcome local tensor-product POVMs and arbitrary normalized positive states. There is no finite-dimensionality or separability assumption. A bounded cross-party commuting PVM representation identity is an additional required root. The lower witness uses actual local Fourier projectors on `C^5 ⊗ C^5`.

The target does not concern arbitrary abstract commuting POVMs, other outcome counts, uniqueness or self-testing. None of those extensions is needed or asserted.

## Publication identity and toolchain

The bootstrap [freeze receipt](verification/formalization_development/bootstrap/FREEZE_VERIFIED.json) records the annotated v0.1.1 tag object `54dc6cabee9b272dd35da736ef9a2208fc715bb8`, peeled commit `73b99dd22af68bd7a10927124d0b4ea7d6e8b78f`, and initial tree `4f5d801bd2ee973493355eca9fc425af116c6081`. The frozen tag history and exact scientific data remain unchanged. The current paper source, bibliography and PDF include separately reviewed prior-work maintenance from upstream commit `1e3282749c9fce2163aaeb8415d8936db88d43ad`, including the Acín–Durt–Gisin–Latorre reference. This is not a claim that the current whole paper is byte-identical to v0.1.1. The [editorial integration receipt](docs/CURRENT_MAIN_EDITORIAL_INTEGRATION.json) records the approved changed files and confirms that the mathematical theorem/proof/data sections are unchanged. The canonical mathematical target remains the frozen v0.1.1 theorem and handoff, rather than any newly substituted statement.

The [toolchain receipt](verification/formalization_development/bootstrap/TOOLCHAIN.json), [Lean pin](lean/lean-toolchain), [Lake configuration](lean/lakefile.toml), [dependency manifest](lean/lake-manifest.json), and [CI pins](verification/lean/ci/pins.json) specify:

- Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`;
- Lake 5.0.0-src+5045d00;
- mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`;
- official Lean Linux archive SHA-256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`;
- Lake manifest SHA-256 `96b577b765d936e10a36a561304d42cb13e0a01feec4681ba18c495e03b95116`.

Package version metadata alone does not establish completion or authorize a v0.2.0 release. Acceptance requires the mathematical and external receipt gates described below.

## Mathematical model

`Strategy.{u,v}` packages local types at arbitrary universes, complete complex inner product spaces, a state on `HTensor Alice Bob`, and two settings of local POVMs. `HTensor` is the Hilbert completion of the algebraic tensor product, with a proved bounded tensor-map construction. `POVM` has five nonnegative bounded effects summing to identity.

`State` is the manuscript-permitted normalized positive complex-linear functional on the full bounded-operator algebra. Universal theorems are not restricted to vector states, normal states or density matrices with separable support. A vector-state constructor is used only to exhibit the lower witness. A separate trace-class constructor is not asserted by this report; the mechanically quantified model is the manuscript's broader positive-functional formulation.

`jointProbability` evaluates genuine local tensor-product effects. `cglmp` uses the literal eight event families through an integer coefficient table divided by two. `cglmp_eq_expect_bell` identifies the literal probability expression with the corresponding bounded Bell operator. `Strategy.lift` transports the concrete finite witness to every universe pair without changing its value.

## Dependency structure

The following is a mathematical dependency DAG. File-level import ordering is computed separately by the clean-build tooling.

1. **Literal convention:** `Events` defines outcomes, settings, modular equalities and `cglmp`; it proves deterministic and convex local bounds.
2. **Actual embedding:** `Root` proves root existence, branch selection, the cubic relation, positive radicals and the exact complex phase.
3. **Scalar interpretation:** pure `ScalarSyntax`, `ScalarTableData` and `ScalarPowerData` define exact arithmetic; `ScalarDefs`, `ScalarEncoding`, `ScalarTable`, `Scalar` and `ScalarConstants` supply actual complex evaluation soundness. Pure data do not import trigonometric analysis merely to compute integer certificates.
4. **Ordered words:** `WordSyntax`, `Words` and `SourceWordBridge` interpret source labels and prove reduction soundness with only the stated order-five, unitary and cross-party commutation relations.
5. **Source and finite identity:** `CertificateChunks`, the `CertificateChunk*` checks, `SourceDecimalSoundness`, `CertificateHeaderSyntax/Data/Proofs`, `CertificateSource` and `CanonicalData` bind exact integers to the canonical source. The phase-compressed data, feature fibers, integer residuals, polynomial semantics and `SOSTarget` feed the checked `SOS.compact_identity` root.
6. **Actual positivity:** `ScalarIntervals`, `EmbeddingBounds` and `Positivity` prove that all 14 source-decoded weights are real and strictly greater than `1/3000` in the selected embedding.
7. **Universal analysis:** `Operator`, `POVM*`, `Tensor`, `Spectral`, `Fourier`, `BellBridge` and `OperatorUpper` turn a checked identity into bounded-operator and local-POVM bounds without dimensional restrictions.
8. **Physical lower bound:** the `Attainment*` modules establish all local Fourier projectors, exact Schmidt amplitudes, normalization, all full-space Bell coordinates, and the literal attained value. `TensorFinite` supplies a full tensor-coordinate equivalence.
9. **Final assembly:** `Strategy`, `StrategyTransport` and `LowerValue` provide the full model, universe transport and lower membership. `OperatorTheorem` supplies the unconditional universal upper results; `Main` supplies `strategy_value_le_mu`, `quantumValues_isGreatest`, `quantumValue_exact` and `cglmp5_exact`.

The [statement preflight](verification/formalization_development/statement_preflight/README.md) checked independent local universes, unrestricted state/POVM interface types, the literal five-dimensional local witness and conditional final supremum assembly. It predates final root assembly and kept the upper bound as an explicit hypothesis. It is retained as interface evidence and is not an audit or a substitute for the subsequently checked unconditional root.

## Proof-source and component results

| Component | Present status | Main declaration or endpoint |
| --- | --- | --- |
| Literal events and local bound 2 | Checked component | `coefficient_cyclic`, `cglmp_local_bound`, `cglmp_zero_assignment` |
| Largest actual sextic root and physical phase | Checked component | `sextic_mu`, `mu_largest_root`, `mu_cubic`, `zeta_eq_exp` |
| Complete scalar multiplication and power interpretation | All 24 rows/576 products and aggregate interpretation checked | `Scalar.eval_mul`, `Scalar.eval_pow`; [freshness receipt](verification/formalization_development/scalar_bridge_freshness.log) |
| Literal SOS target evaluation | Checked component | `SOSFinite.target_evaluation` |
| Canonical compact source decoding | Checked component | `canonical_source_decode`, `canonical_text_decode` |
| Numeric header decoding and provenance | Checked component and actual-byte readback | `header_gamma_text_decode`, `header_mu_box_text_decode`, `header_s_box_text_decode`, `header_u_box_text_decode` |
| Actual source byte readback | Checked development readback | 581,335 bytes; canonical SOS14 SHA-256, as below |
| Ordered word interpretation | Checked component | `Word.evalStar_mul`, `Word.evalStar_adjoint`, `rawCoefficient_eval` |
| Positive actual weights | Checked component | `weight_gt_one_div_three_thousand`, `weight_evaluation` |
| Sparse integer phase arithmetic | All 480 generic formulas checked | the 480 `phase_linear_e_k` family members (indices e=0,…,19 and k=0,…,23), aggregate module `SOSPhaseLinear` |
| Phase and word support checks | All component aggregates checked | `SOSPhaseChecks`, `SOSExpansionChecks`, `SOSIndexFiberChecks` |
| Actual compact SOS identity | Production aggregate checked | `SOS.compact_identity`; all 273 residuals, reflection, source/phase semantics and target interpretation supplied |
| Generic bounded-state and POVM transfer | Checked conditional interfaces | `operator_bound_of_sos`, `tensor_povm_bound_of_unitary_bound` |
| Explicit physical attainment | Checked component | `Attainment.explicitStrategy_value`, `Attainment.physicalVector_eigen` |
| Arbitrary-universe lower membership | Checked component | `mu_mem_quantumValues` |
| Unconditional universal upper | Production build checked | [OperatorTheorem receipt](verification/formalization_development/operator_theorem_build.log) |
| Final exact supremum/Main | Production build checked | [Main/root build receipt](verification/formalization_development/main_root_build.log); full family in [Source Map, layer 9](SOURCE_MAP.md#handoff-layer-9-and-final-theorem-assembly) |
| Complete production-module/public-root build | Development build checked | [Complete build receipt](verification/formalization_development/main_all_modules_build.log) |
| Independent replay, exact axioms, audits, CI and release acceptance | Established only by external same-tree receipts | No final acceptance inferred from component builds |

## Exact source decoding and arithmetic

The primary finite route uses the immutable `SOS14.json`: 14 weights and 164 stored polynomial coefficients. Its long integer strings are represented as ordered fragments of at most nine decimal digits. Each fragment is checked by the total ASCII decimal parser; fragment accumulation uses exact base-10 arithmetic. `DecimalChunks.natural_sound` and `integer_sound` prove that successful fragmented decoding agrees with the uninterrupted decimal text, including the sign. `ChunkScalar.decode_sound`, `ChunkCoefficient.decode_sound` and `ChunkTerm.decode_sound` lift this fact to the full typed records.

All 178 scalar checks and 14 term checks have passed, followed by the aggregate source decoding theorems. The [actual Lean-value readback](verification/formalization_development/LEAN_SOURCE_BYTES_READBACK.json), dated 12:58:22 UTC, reconstructs `canonicalSourceBytes` as exactly 581,335 bytes with SHA-256 `1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2`. This external byte/hash comparison is a provenance check paired with the kernel decoding theorems; it is not a formal SHA-256 implementation or a substitute for the scientific identity. Acceptance requires the same check on the frozen candidate.

The term records and numeric header records now have kernel decoding bridges. The five gamma scalars and all twelve embedding-box integer strings use the same lossless chunks in `CertificateHeaderSyntax`, `CertificateHeaderData` and `CertificateHeaderProofs`. `header_gamma_text_decode` and the three `header_*_box_text_decode` theorems connect uninterrupted source strings to the exact typed records. `canonicalHeaderPrefix` renders these checked strings. The revised `canonicalSourceBytes` now uses `headerLines`; a fresh [actual Lean-value readback](verification/formalization_development/LEAN_SOURCE_BYTES_READBACK_HEADER.json) at 13:26:20 UTC again produced exactly 581,335 bytes and the canonical SHA-256 with empty stderr. It independently checked all five gamma records and all three boxes from the emitted chunks, in addition to the 178 term scalars. Acceptance requires repeating the source check on the final frozen tree. Header decoding itself passed the [component build](verification/formalization_development/header_build.log).

The scalar evaluator uses the ordered 24-coordinate family from the handoff. Formal reductions are interpreted at actual complex numbers through proved evaluation rules; neither irreducibility nor injectivity of a quotient presentation is assumed. Source denominators have checked positivity. Header status strings and historical solver claims are not theorem premises.

The current finite implementation compresses the same 14 polynomials into 28 phase orbits and 135 weighted core-pair coefficients. It expands 4,320 ordered features into 273 normal-word fibers. These are implementation factorizations of the compact certificate, not replacements by a numerical Gram matrix. The 480 generic integer phase lemmas reduce each coordinate multiplication to at most four live terms. Denominator clearing, exact sparse arithmetic and opaque lookup equalities reduce kernel memory without changing the equations.

All 273 production integer-residual leaves have now passed across the two coordinated replay ranges. The residual aggregate and actual `SOS.compact_identity` integration have also passed; see the [identity build receipt](verification/formalization_development/sos_identity_build.log). A successful generator computation or isolated staging benchmark is not treated as proof of those aggregate roots. Preserved [development experiments](verification/formalization_development/residual_pilot/README.md) distinguish failed runs from the checked fallback and production optimizations.

The positivity proof independently uses proved rational boxes for the actual root and radicals. Its boxes may be wider than the frozen narrow serialization boxes, as explicitly permitted in `ROOT_EMBEDDING.md`; all required enclosure and strict positivity facts are reproved. The auxiliary Gram/LDL data remain frozen references, not unverified premises of this compact route.

## Explicit full-space lower strategy

The two local spaces are literally `EuclideanSpace ℂ (Fin 5)`. `alice_fourier_formula` and `bob_fourier_formula` identify the actual projectors' component vectors with the manuscript offsets `(0,1/2)` and `(1/4,-1/4)`, including Bob's negative outcome sign. `Attainment.fourier_orthonormal`, `Attainment.localProjection_sum` and `Attainment.localProjection_positive` prove orthogonality, completeness and positivity for all four measurements; `Attainment.localPVM` packages the PVMs used by the explicit strategy.

The Schmidt coefficients `(1,a,b,a,1)` are positive; the denominator defining `a` is greater than 4. `Attainment.canonical_gamma` connects the common source decoder to the same amplitudes. `Attainment.canonical_header_gamma_evaluation` further proves that parsing the uninterrupted decimal strings rendered in the numeric header and evaluating them yields those exact amplitudes. `state_apply` and `state_norm` describe the normalized vector on all 25 product-basis coordinates.

Every Bell word's off-diagonal output is proved to vanish on diagonal Schmidt inputs. All 25 remaining matrix entries and the exact row equations are checked. `state_eigen` is a full 25-dimensional relation, and `physicalVector_eigen` transports it through the full `CGLMP5.tensorEuclideanEquiv` Hilbert-tensor isometry before taking an expectation. `CGLMP5.tensorEuclideanEquiv_operator_kronecker` supplies the all-coordinate tensor/matrix operator identity. `literalBell_coordinates` connects this operator to the original probability convention. The [attainment source map](docs/LEAN_ATTAINMENT_SOURCE_MAP.md) gives the detailed path.

## Trusted boundary and verification gates

The mathematical proof boundary is Lean's kernel with the pinned library dependency graph. Python generators may propose explicit integers, tables and proof scripts, but their output must be checked by Lean. No numerical solver, floating eigensystem, external polynomial calculation, cached PASS flag or code-generation assertion is accepted as a premise. The detailed [SOS source map](docs/LEAN_SOS_SOURCE_MAP.md) records the complete chain from typed compact records through finite reflection to the actual representation identity. `decide +kernel`, `norm_num`, `ring` and `linear_combination` are used for kernel-visible proofs; no project-specific axiom, `sorry`, `admit`, proof-critical `unsafe` or `native_decide` is permitted in the accepted dependency graph.

Exact per-root axiom sets are **not inferred** from this description. The [inspection inventory and procedure](verification/lean/README.md) require fully printed types, exact `#print axioms` output and an independent imported-object kernel replay on the final candidate. The pinned official `leanchecker --fresh` route is required for that replay; `lean --trust=0` alone must not be described as rechecking every imported proof. The allowlist is `propext`, `Classical.choice` and `Quot.sound`; the final report must record which declarations actually use each. The authoritative per-declaration results belong in `AXIOM_AUDIT.md` and the machine-readable inspection receipts; they are not inferred from this allowlist.

Development negative controls include wrong event shifts, same-party commutation, incorrect root/weight signs, proper-isometry surjectivity, setting-dependent embeddings, compression multiplicativity and compressed-only attainment. Additional checked lower controls exhibit a Bell perturbation invisible to diagonal compression, a wrong Fourier offset, and a genuinely renormalized corrupted Schmidt vector that is not an eigenvector. Their [development receipt](verification/lean_negative_controls/runs/20261004T120258Z/receipt.json) is historical, not a final-tree audit. Actual SOS coefficient corruption must also be rejected by the completed scientific proof path.

The [clean replay instructions](docs/LEAN_REPLAY.md) require a relocated clean checkout, pinned runtime verification, source reconstruction, every production module, the final umbrella build, exact trust inspection and all mutation controls. The final three audits must start only after full theorem closure and must pass sequentially on one identical Git tree. Any source-tree change invalidates prior rounds for the new candidate. Integrated-commit CI, annotated publication, downloaded-asset verification and backup acceptance are governed by the external receipt contract below.

## External acceptance receipt contract

This source document describes mathematical declarations and required verification. It does not serve as its own audit, CI or release receipt. Acceptance of a candidate is established only by external records identifying that candidate's exact Git tree and source hashes:

1. **Completion and replay:** an unconditional full theorem-family build, the complete production-module build, exact root/bridge type and axiom inventory, pinned-runtime checks, official independent imported-object kernel replay, source-byte reconstruction, and required negative controls. The replay record must state the exact `leanchecker --fresh` invocation and coverage; a `--trust=0` invocation alone cannot establish imported-proof replay.
2. **Three sequential audits:** three separate adversarial reports, each identifying the same candidate tree and recording its own checks, findings and outcome. A later round begins only after the preceding round has passed. Any source-tree change invalidates previous rounds for the new candidate; all three accepted rounds must concern the identical final tree.
3. **Integrated CI:** the successful CI run must identify the integrated commit and corresponding accepted tree, including the canonical-input hashes and verification commands. A component log or workflow definition alone does not establish CI success.
4. **Release and recovery:** publication receipts must identify the annotated v0.2.0 tag/commit, released assets, independently downloaded asset hashes and final restorable backup. A planned tag or uploaded filename alone does not establish correct publication or restoration.

These records may be produced after this document is frozen. Their presence and success are established by the records themselves, without editing this source document to append later PASS labels. Missing, failed, mismatched-tree or incomplete records do not satisfy the contract.

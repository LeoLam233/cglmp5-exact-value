# Canonical source map for the later Lean milestone

This is a handoff and source map only. **No Lean formalization is started or claimed in v0.1.1.** The eventual completed formalization milestone is reserved for `v0.2.0`.

## Freeze the publication identity first

The next task must begin from the **remotely verified** annotated `v0.1.1` tag, not an uncommitted checkout or a moving `main` branch. The final annotated tag object, peeled commit, default-branch integration, manuscript/source hashes, CI result, Codex contributor verification and downloaded release-asset hashes are recorded after publication in the additive release asset **`REMOTE_VERIFICATION.json`**. That receipt is produced after the tagged commit and is not claimed to have existed inside the commit it identifies. It cannot recursively authenticate its own final asset digest.

The tagged [`verification/release_gate.json`](../verification/release_gate.json) and associated hashed receipts identify R01–R14. The manuscript build instructions and result are in [`paper/README.md`](../paper/README.md); its source and compiled PDF must match the source/PDF hashes in the final remote receipt. A tag, a local build or a summary PASS alone does not satisfy the publication freeze. Verify the remote receipt and assets before using this map for a new task.

## One mathematical target

Use the standard five-outcome CGLMP functional with local bound 2, two measurement settings at each party, outcomes `0,...,4`, modular event shifts and the `k=0,1` weights `1-k/2`. The theorem is

`sup I_5 = mu`, where `mu` is the largest real root of
`5 mu^6 - 65 mu^4 + 144 mu^2 + 96 mu + 16 = 0`.

The full scope is arbitrary local Hilbert-space dimensions and arbitrary **local tensor-product five-outcome POVMs**, with an explicit attainer on `C^5 tensor C^5`. The operator upper identity also applies to bounded cross-party commuting PVM representations. Do not substitute a claim about arbitrary abstract commuting POVMs, arbitrary outcome number, self-testing, uniqueness or a finite-dimensional cutoff.

Canonical exposition is the standalone [`paper/main.tex`](../paper/main.tex), reconciled against the frozen [`artifact_v0.1/PROOF.md`](../artifact_v0.1/PROOF.md). The latter and its four JSON tables define the immutable mathematical baseline. The new [`artifact_v0.1.1/`](../artifact_v0.1.1/) is the versioned verification interface with expanded bridge/schema documentation; it does not define a changed polynomial, coefficient list or physical strategy.

## Canonical finite data

All four JSON files in `artifact_v0.1.1/` are byte-identical to their `artifact_v0.1/` counterparts. Read integer strings as exact integers, never via a floating intermediate. A scalar is a 24-coordinate numerator and positive integer denominator in the ordered spanning family

`n[a+2b+6c+12e] * s^a x^b u^c i^e / d`,

where `s=+sqrt(5)`, `x=5 mu`, `u=+sqrt(10+2s)`, `a,c,e in {0,1}` and `b in {0,1,2}`.

| Object | Canonical file | SHA-256 | Role |
|---|---|---|---|
| Compact exact certificate | `artifact_v0.1.1/SOS14.json` | `1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2` | Fourteen positive weights and polynomials; 164 stored nonzero scalar coefficients in the frozen table; physical state and embedding boxes |
| Auxiliary kernels/basis | `artifact_v0.1.1/EXACT_KERNELS.json` | `6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5` | 81-word basis, five E blocks and state data |
| Auxiliary Gram coefficients | `artifact_v0.1.1/EXACT_SOS_CANDIDATE.json` | `14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649` | Five H blocks; historical discovery status is non-authoritative |
| Auxiliary LDL/positivity data | `artifact_v0.1.1/POSITIVITY_CERTIFICATE.json` | `22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de` | H=L D L* and actual-embedding rational enclosures |

The manuscript additionally prints a complete factorized Gram representation in `paper/phase_supports.tex`, `paper/kernel_data.tex`, `paper/parameter_assignments.tex`, `paper/parameter_data.tex` and `paper/minor_bounds.tex`. `paper/check_paper_data.py` checks the printed F/K/H data against the canonical JSON, the full Gram identity, the compact coefficients/weights, actual leading-minor positivity and physical attainment. These printed data are an equivalent explanatory presentation; the exact JSON byte identities above remain the machine-readable baseline.

The compact certificate is sufficient for the SOS upper bound when its identity and actual strict positivity are proved. Gram/LDL is redundant data-path coverage; the fourteen D values coincide with the compact weights. No solver/discovery program, optimizer convergence or numerical rank is a premise of the finished finite identity.

## Recommended proof dependency map

1. **Definitions and literal event convention.** Take the eight event families, modular shifts `D0=A0`, `D1=B0`, `D2=A1+1`, `D3=B1+1`, `f(z)=1-z/2`, and Fourier target from the manuscript/frozen proof. Reconstruct the literal probability coefficients rather than trusting the operator expression alone. `verify_independent.py::verify_physical` and the Phase-B `attainment/exact_linkage.py` are executable reference checks, not already formalized lemmas.
2. **Actual scalar interpretation.** Define `mu` by its exact polynomial and unique root above 3; prove the endpoint signs and monotonicity. Define positive `s,u` and `zeta=(u+i(s-1))/4`, then prove the algebraic relations and the physical root-of-unity branch. Consult `ROOT_EMBEDDING.md`, `verify_statement.py` and `verify_independent.py`. A reduction to formal zero is sound under an evaluation homomorphism even without irreducibility; it does not by itself prove root selection, realness or positivity.
3. **Exact algebra and scalar encoding.** Interpret all 24-coordinate rationals exactly. Either retain the tower representation or establish a proved map to the cyclotomic/cubic spanning family `zeta^a x^b`, `0<=a<8`, `0<=b<3`, reducing by `Phi_20(z)=z^8-z^6+z^4-z^2+1` and the cubic relation for x. The existing Python engine provides a reference algorithm, not a trusted Lean kernel extension. Prove every denominator used in actual formulas is nonzero.
4. **Noncommutative word semantics.** Preserve same-party order. Only cross-party commutation and each generator's order-five/unitary relations are available. Reference `canon`, `star` and `word_product` in `verify_independent.py`. Show that reduction preserves evaluation before relying on a reflected finite calculation. Compact expansion touches 273 word positions; the auxiliary full Q*Q Gram universe has 1,681. These are different sets, not inconsistent counts.
5. **Finite SOS identity and positivity.** Import/reflect the compact table and prove `mu I-B=sum_j d_j(R_j* R_j+R_j R_j*)`. Prove each weight is real and strictly positive in the actual embedding. The frozen rational boxes suffice when their endpoints and propagation are proved. Phase-B's independent Sturm–Tarski/Fraction route proves every weight greater than `1/3000` and can guide an alternative exact sign implementation. Do not replace this by finite-field or floating checks.
6. **Bounded-operator upper bound.** Interpret the identity in an arbitrary bounded *-representation and use positivity of `R*R` and `RR*`. Extend to every normalized positive state as required, without a finite-dimensional or pure-state restriction. Clearly distinguish this analytic library interface from the finite certificate checker.
7. **Fixed-common-space POVM bridge.** Use one local embedding `J` for both measurement settings. Separate-complement completion, or the explicit proper-isometry defect construction in [`artifact_v0.1.1/POVM_BRIDGE.md`](../artifact_v0.1.1/POVM_BRIDGE.md), preserves every compressed effect and every joint tensor-product operator. Do not assume `VV*=I` for a proper isometry or that compression is multiplicative. The proof must cover infinite/nonseparable local spaces and the stated state model; finite matrix tests do not establish these quantifiers.
8. **Full-space attainment.** Define the four Fourier measurements with exact offsets `(0,1/2)` and `(1/4,-1/4)`, prove orthonormality/completeness, define the positive Schmidt coefficients `(1,a,b,a,1)` and normalize. Prove the full 25-dimensional Bell eigenvector relation, not merely the 5-dimensional compressed relation. The denominator for a exceeds 4. The 28 vectors `R_j psi` and `R_j* psi` provide additional exact linkage checks.
9. **Assembly and assumptions audit.** Combine lower and universal upper bounds, list analytic dependencies and the trusted proof kernel/toolchain, and ensure no axiom or admitted placeholder is reported as a proof. Only the later completed and independently checked formalization should support a `v0.2.0` claim.

This is a suggested decomposition, not permission to weaken the theorem to suit existing library coverage. The future task should identify genuinely missing formal interfaces explicitly.

## Independent reference routes in the immutable Phase-B archive

Paths below are relative to the final Phase-B archive root. The archive hash and full source/evidence path crosswalk are in [`PROVENANCE.md`](PROVENANCE.md) and [`PHASE_B_ERRATA.md`](PHASE_B_ERRATA.md).

| Interface | Phase-B reference source |
|---|---|
| Literal target / full physical linkage / saturation | `outputs/INDEPENDENT_CHECKS/attainment/exact_linkage.py` |
| Non-box algebraic signs | `outputs/INDEPENDENT_CHECKS/field/sturm_tarski_weights.py` |
| Separate Fraction sign implementation | `outputs/INDEPENDENT_CHECKS/field/fraction_sign_meta.py` |
| Scalar/physical representation cross-map | `outputs/INDEPENDENT_CHECKS/field/review_attainment_field.py` |
| Auxiliary Gram–compact linkage | `outputs/INDEPENDENT_CHECKS/field/gram_elimination_recheck.py` |
| Expanded-letter normal-form control | `outputs/INDEPENDENT_CHECKS/nc/cross_audit_normal_forms.py` |
| Finite-field concrete matrix diagnostic | `outputs/INDEPENDENT_CHECKS/nc/finite_field_matrix_attack.py` |
| Exact fixed-common-J controls | `outputs/INDEPENDENT_CHECKS/bridge/exact_common_space.py` |
| Proper-isometry defect block | `outputs/INDEPENDENT_CHECKS/bridge/formal_isometry_bridge.py` |
| Compression nonmultiplicativity control | `outputs/INDEPENDENT_CHECKS/bridge/compression_product_attack.py` |
| Analytic universal bridge | `outputs/lanes/bridge/ANALYTIC_UNIVERSAL_BRIDGE.md` |

Use the corrected evidence interpretation. Do not import A07's setting-dependent state test, aborted modular-size bound or floating positivity as a proved interface; do not import A06's reversed generic word evaluator or invalid abelianization as the target semantics. Original failed attempts remain valuable regression fixtures, with their failure status intact.

## Verification and attribution boundaries

R01–R14 and the v0.1.1 remote verification receipt document the executable acceptance gate and publication state. They are neither Lean proofs nor human peer review. Codex's GitHub repository contribution credit is separate from manuscript authorship; Dehao Lin remains the human author. A formalization task must preserve these distinctions and retain the frozen v0.1.0/v0.1.1 artifacts rather than rewriting them.

# C001 first frozen physics/convention audit

This is an adversarial audit of the frozen `audit_view`, not a vote on the full certificate. No established counterexample, load-bearing error, or specific remaining gap was found in the probability convention, root selection, physical attaining strategy, dimension-independent positivity implication, or simultaneous local POVM dilation arguments examined here. The universal upper bound remains conditional in this report on the noncommutative SOS identity and strict positivity of its weights; I did not independently expand that universal identity or prove the 14 weights positive. The strong exact attainment consistency tests below do not replace those tasks.

## Boundary, exposure, and reproducibility

The first files read were `AUDIT_CONTRACT.md` and `INPUT_IDENTITY.json`. I then read `PROOF.md` sections 1–6 and `ROOT_EMBEDDING.md`. I parsed `SOS14.json` to test all 14 serialized polynomials against the physical attaining vector. The other six scientific files were only hashed as bytes: I neither read their implementations/content semantically nor imported or executed the supplied verifiers. No history, generation code, memory, candidate directory outside `audit_view`, or other agent's receipts was read. The analytic arguments and the new arithmetic implementation were written in this audit. No scientific input was modified or published.

All nine scientific byte hashes match `INPUT_IDENTITY.json`:

| File | SHA-256 |
|---|---|
| `EXACT_KERNELS.json` | `6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5` |
| `EXACT_SOS_CANDIDATE.json` | `14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649` |
| `POSITIVITY_CERTIFICATE.json` | `22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de` |
| `PROOF.md` | `41737b9607c945ba3be463383a1b0bcb96e43404c326f6e114a6bb6dc6d88ff7` |
| `ROOT_EMBEDDING.md` | `81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119` |
| `SOS14.json` | `1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2` |
| `verify_independent.py` | `8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3` |
| `verify_sos14.py` | `90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094` |
| `verify_statement.py` | `b94e281b07a63224b95fa2ece2482f5ed774c99fa461d51a37f0a61c8ac76d37` |

`input_hashes.json` additionally records the contract and identity file hashes. The portable replay script accepts the frozen input directory as an optional positional argument; the relative default is `../../audit_view` from the receipt directory. It uses Python standard-library exact `Fraction` arithmetic for every convention, algebra, Bell-matrix, root, and SOS annihilation check. Only the explicitly labeled finite Naimark diagnostic uses NumPy. SymPy was unavailable, so no symbolic-engine result is being relied on.

Actual executed command, exit code 0:

```powershell
& 'python' '<LOCAL_POST_VERIFICATION>\receipts\audit_physics\audit_exact.py' '<LOCAL_POST_VERIFICATION>\audit_view' 2>&1 | Tee-Object -FilePath '<LOCAL_POST_VERIFICATION>\receipts\audit_physics\executed.log'
```

The final executed log and machine-readable `results.json` are preserved alongside this report. `FREEZE_MANIFEST.json` records the first-report freeze and receipt hashes. This report was frozen before reconciliation with another audit.

## 1. Standard CGLMP events, shifts, and phases

The load-bearing attack was that a sign or outcome shift could make an apparently exact SOS bound target a different Bell functional. I reconstructed the weights from the eight standard events, without using the cyclic expression. For a particular setting pair and outcomes `(a,b)`, the weights obtained are:

| Setting pair | Weight |
|---|---|
| `(0,0)` | `f([a-b]_5)` |
| `(1,0)` | `f([b-a-1]_5)` |
| `(1,1)` | `f([a-b]_5)` |
| `(0,1)` | `f([b-a]_5)` |

Here `f(r)=1-r/2`, so its values are `(1,1/2,0,-1/2,-1)`. All 100 setting-pair/outcome weights agree exactly with the shifted cyclic expression. This entails equality for every correlation, including signaling ones; no quantum assumption is used in this comparison. A separate enumeration of all 625 deterministic assignments verifies the same total expression and maximum 2. Analytically, the four cyclic residues sum to `4 mod 5`, are nonnegative, and hence sum to at least 4. The all-zero original outputs attain 2.

For `omega=exp(2*pi*i/5)`, the independently computed DFT is

`c_k=(1/5) sum_{r=0}^4 f(r) omega^(-kr)`.

The geometric sum gives `c_0=0` and `2(1-omega^(-k))*c_k=1` for each nonzero `k`; thus the reciprocal formula has the correct sign. On a joint spectral event of a cross-party pair, `U_r^k U_s^(-k)` has eigenvalue `omega^(k(D_r-D_s))`. Consequently DFT inversion produces `f([D_r-D_s]_5)`. For the last edge the extra scalar `omega^(-k)` produces `f([D_3-D_0-1]_5)`. The proof's `D_2=A_1+1` and `D_3=B_1+1` are essential: the second edge is `b-a-1`, while the last edge simplifies to `b-a`.

I independently built the full 25-by-25 Bell operator in two ways: directly by summing all standard probability weights times Fourier projector tensor products, and by evaluating the stated noncommutative generator polynomial with the `D` outcome shifts. All 625 entries agree exactly. The result is Hermitian and has 60 nonzero entries. Deliberate mutations removing the last phase, reversing the last phase, removing the `A_1` outcome shift, or removing the `B_1` outcome shift each cause exactly 100 matrix-entry mismatches. These controls show that the comparisons can detect the convention errors under attack.

## 2. Algebraic root and coefficient branch

The sextic's derivative for `t>=3` is

`p'(t)=t^3(30t^2-260)+288t+96>0`,

because `30t^2-260>=10`. Since `p(3)=-20` and `p(31/10)>0`, there is one root in `(3,31/10)` and none larger. Calling this root the largest real root is justified without needing to count roots below 3. I independently bisected the rational interval 256 times, checking exact signs. The resulting endpoints happen to coincide with the serialized endpoints; the algorithm did not read those boxes.

Exact polynomial multiplication verifies

`[5(t^3-4t-4)]^2 - 5(5t^2-4t-8)^2 = 5 p(t)`.

For `t>=3`, both displayed unsquared quantities are strictly positive (values at 3 are 55 and 25, with positive derivatives thereon). The root therefore obeys the positive square-root branch

`mu^3=s*mu^2+(4-4s/5)*mu+(4-8s/5)`, `s=+sqrt(5)`.

The phase branch is likewise sufficient: with `u=+sqrt(10+2s)`, `z=(u+i(s-1))/4` has modulus 1, satisfies `z^5=i`, has positive imaginary part and real part larger than `1/sqrt(2)`. Among the five roots of `z^5=i`, only the angle `pi/10` satisfies these inequalities. The branch is not inferred from a decimal approximation.

My arithmetic represents scalars in `Q[z,mu]` modulo `z^8-z^6+z^4-z^2+1` and the displayed cubic. It independently checks `s=2(z^2+z^-2)-1`, `u=2(z+z^-1)`, `i=z^5`, all square relations, the actual radical expression for `z`, conjugation, and `z^20=1`. Polynomial reduction to zero is sufficient for an identity at these actual numbers even if the quotient presentation is reducible. No inverse of an uncertain algebraic element was used in the exact eigenvector or SOS-vector calculations.

## 3. Legality and full-space attainment

The 100 inner products across the four supplied Fourier bases are exactly those of orthonormal bases. Hence they define complete rank-one projective measurements with the stated outcome numbering. The local generator matrices were rebuilt by summing those projectors with their `D` spectral phases, rather than postulating shift matrices.

Directly from the probability expression, the full Bell matrix preserves each of the five sectors `j-m mod 5`. This was checked on every nonzero entry. The sector containing `|jj>` is therefore invariant for the specific strategy. Its matrix has diagonal zero and off-diagonal `f_|j-l|`, with the four `f` values of the proof. All 25 compressed entries were checked exactly.

For a symmetric vector `(e,a,b,a,e)`, the three independent row equations are

```text
mu*e = f4*e + (f1+f3)*a + f2*b
mu*a = (f1+f3)*e + f2*a + f1*b
mu*b = 2*f2*e + 2*f1*a.
```

For `e=1`, eliminating `b` from the latter two equations gives precisely

`D=mu(mu-f2)-2f1^2`, `A=mu(f1+f3)+2f1*f2`, `a=A/D`, `b=2(f2+f1*a)/mu`.

The characteristic polynomial of the corresponding symmetric 3-by-3 matrix is exactly

`t^3-s*t^2-(4-4s/5)*t-(4-8s/5)`.

Its coefficient equalities were checked independently. This explains why the remaining row equation holds at the actual `mu`.

The denominator is valid analytically: `mu>3`, `0<f2<1`, and `0<f1<1` imply `D>3*(3-1)-2=4`. All numerator terms are positive, so `a,b>0`. The norm squared `2+2a^2+b^2` is strictly positive, finite, and is exactly the squared norm of the displayed unnormalized state. Thus division and normalization are legitimate.

The stronger test did not stop at the compression. I cleared the nonzero denominator using

`G=mu*D*(|00>+a|11>+b|22>+a|33>+|44>)`.

Its five nonzero coordinates are polynomial scalars `(mu D,mu A,2(f2 D+f1 A),mu A,mu D)`. Independently constructing `B` from all probabilities and checking all 25 coordinates gives `B G=mu G` exactly. This rules out unnoticed leakage outside the compressed subspace and establishes a physically legal attained lower bound.

I then attacked the certificate's necessary compatibility with attainment. If a positive identity `mu I-B=sum d_j(R_j^dagger R_j+R_j R_j^dagger)` holds on this vector, every `R_j` and `R_j^dagger` must annihilate it. I decoded all 164 serialized nonzero polynomial coefficients into the new arithmetic and evaluated every ordered word on the full 25-dimensional `G`. All 28 full-vector residuals, covering both actions for all 14 polynomials, are exactly zero. No scalar positivity assumption was used to perform these checks. Their logical strength is necessary consistency at one representation; they do not establish the universal noncommutative identity.

## 4. Why the upper-bound implication covers arbitrary dimensions

Conditional on the exact SOS identity and positive real weights, this step has no remaining finite-dimensional restriction. In any Hilbert-space representation each `U_r` is a bounded unitary, so every finite polynomial `R_j` is a bounded operator. For every vector `h`,

`<h,(R_j^dagger R_j+R_j R_j^dagger)h> = ||R_j h||^2+||R_j^dagger h||^2 >=0`.

Thus `mu I-B` is positive in operator order. The argument applies to arbitrary Hilbert cardinality, including nonseparable spaces, and requires no compactness, approximation, or limit interchange. Finite positive linear combinations of positive bounded operators remain positive. A normalized vector state, mixed density-operator state, or arbitrary positive normalized functional evaluates a positive operator nonnegatively.

This does not assume same-party measurements commute. Cross-party commutation suffices for the Bell products and noncommutative relations. Tensor-product local measurement representations are a special case. The proof's stronger statement about arbitrary commuting projective representations follows from the same SOS evaluation. I found no route by which an infinite-dimensional representation could invalidate an exact finite positive SOS.

## 5. Simultaneous local Naimark construction, including infinite spaces

I unpacked the proposed bridge explicitly to test whether different settings accidentally require incompatible embeddings. For any five-outcome POVM `{E_a}` on an arbitrary Hilbert space `H`, define

`V h = sum_a sqrt(E_a)h tensor |a>` in `H tensor C^5`.

The positive square roots are bounded and `V^dagger V=sum E_a=I`; hence `V` is an isometry with closed range, even if `H` is infinite or nonseparable. Let `K=(ran V)^perp`. The unitary `W:H direct-sum K -> H tensor C^5`, `W(h,k)=Vh+k`, produces projectors

`P_a=W^dagger (I tensor |a><a|) W`

with compression to the original `H` equal to `E_a`.

For two settings make this construction separately, obtaining `K_0,K_1` and projective measurements on `H direct-sum K_x`. Place both on the common space `H direct-sum K_0 direct-sum K_1`. Setting 0 acts by its dilated projectors on `H direct-sum K_0` and assigns the entire unused `K_1` to outcome 0. Setting 1 acts by its dilated projectors on `H direct-sum K_1` and assigns unused `K_0` to outcome 0. Each setting separately remains a complete orthogonal projective measurement; each has the same fixed original inclusion `J:H -> H direct-sum K_0 direct-sum K_1`, and `J^dagger P_a^x J=E_a^x`. No simultaneous joint outcome measurement and no same-party commutation is claimed.

Apply this locally to Alice and Bob. With `J=J_A tensor J_B`,

`J^dagger(P_a^x tensor Q_b^y)J = E_a^x tensor F_b^y`.

For a density operator the lifted state `J rho J^dagger` is positive and trace one; the displayed compression identity preserves every joint probability. Pure states lift isometrically. The dilated cross-party projectors commute by their tensor factors. These assertions remain valid without dimensional or separability assumptions. All operations involve a finite sum of bounded effects and isometric maps.

A diagnostic implementation of this exact construction used random five-outcome POVMs in local dimensions 2 and 3, each with two settings, and common dilated dimensions 18 and 27. With fixed seed `5012026`, the largest projectivity/completeness/compression error was `1.4438714435924383e-15`; the largest difference over all 100 joint probabilities was `6.38378239159465e-16`. This finite diagnostic checks an implementation of the construction only. The infinite-dimensional conclusion comes from the analytic argument above, not this finite experiment.

## Failed attacks, actual scope, and limitations

The strongest reproducible convention attacks were last-edge conjugation and removal of the two shifted outcome encodings. Correct expressions survived exact independent reconstructions; deliberate incorrect expressions failed the mutation controls. The strongest attainment attack was to discard the compression assumption and evaluate the full probability-defined operator on a denominator-cleared state. Its residual vanished in all 25 coordinates. The stronger SOS compatibility attack tested both adjoint directions for every polynomial; all 28 residuals vanished. The common-dilation incompatibility attack was answered by an explicit shared-inclusion construction valid at arbitrary Hilbert cardinality.

No demonstrated counterexample, proof error, or specific unresolved physical-convention gap emerged within this scope. A general five-dimensional/Fourier optimality ansatz would have been unjustified as an upper-bound method. The proof does not need such an ansatz if its stated universal positive SOS is validated: the Fourier strategy supplies only attainment. I have not promoted a fixed-strategy calculation into the unrestricted upper bound.

The theorem's scope is five outcomes and two settings per party for local tensor-product POVMs; the SOS also covers the stated commuting-projective operator model. This audit establishes no measurement uniqueness, self-testing, all-outcome theorem, or statistical-optimality statement. It does not audit experiments, general contextual measurements, or nonlocal POVMs. It did not formally verify the new Python interpreter/arithmetic or use a proof assistant. The report is an independently reproducible analytic and exact-computation audit of the specified downstream claims, with the universal certificate identity and strict weight positivity explicitly left to their own audit.

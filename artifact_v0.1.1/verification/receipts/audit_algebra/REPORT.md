# C001 algebra audit — first report

Frozen-input audit, 2026-10-04. The delegated scope is exact algebra and verifier soundness in the supplied isolated audit view. I found no counterexample to the claimed upper bound and no load-bearing algebra error in the supplied certificate. I found one reproducible, non-load-bearing input-schema weakness in the supplied parser. This report does not claim exhaustive verification or an external formal proof.

## Input identity and exposure

I read `AUDIT_CONTRACT.md` and `INPUT_IDENTITY.json` first. Scientific inputs read were exclusively the following files in `post_verification/audit_view`. Their byte hashes were independently recomputed and matched the supplied identity file.

| File | SHA-256 |
| --- | --- |
| EXACT_KERNELS.json | 6e08746bf5a58addb6bb46beb00c7bdab29638b9290802bca5114bc47ae957a5 |
| EXACT_SOS_CANDIDATE.json | 14324f3ea10a3b1304a02ce48b5572be7080b519c242f5802ed599f60325c649 |
| POSITIVITY_CERTIFICATE.json | 22ba8a09e433fe269b805f9979f574e37e3262a33fdae5a71927b748a860e8de |
| PROOF.md | 41737b9607c945ba3be463383a1b0bcb96e43404c326f6e114a6bb6dc6d88ff7 |
| ROOT_EMBEDDING.md | 81d1c2ba6bd17bdf358c24f61ef569774e9b8916149221d76c139a89f1e5a119 |
| SOS14.json | 1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2 |
| verify_independent.py | 8aa54411ec9bbc79245e6e42db79a698dfcd11eb9853f331ac8221a662244fc3 |
| verify_sos14.py | 90bef7e72619c99222a08003ba5d0ab204b08cde021daf28cdc86aaa09281094 |
| verify_statement.py | b94e281b07a63224b95fa2ece2482f5ed774c99fa461d51a37f0a61c8ac76d37 |

I also read the audit contract and identity manifest, and my newly generated scripts and outputs. I did not read another agent's outputs, prior discovery code, success reports, candidate/history/review directories, or the full proof outside this view. The coordinator's procedural messages concerned portability and freezing the report; they supplied no scientific results from other reviewers. The supplied proof itself contains success assertions, treated as claims under audit rather than evidence. New files are confined to this receipt directory. No supplied scientific file was edited. Bytecode writes were disabled for all replays/imports.

## Covered load-bearing paths

The upper-bound path examined was: encoded coefficients → actual real/cyclotomic embedding → a valid noncommutative polynomial identity → positive real weights or positive Gram blocks → positive operators in any representation. I examined the physical strategy as a consistency and falsification probe; the complete POVM and infinite-dimensional scope is primarily the coordinator's statement audit, though the SOS implication itself was checked mathematically here.

### Coefficient arithmetic and embedding

`audit_exact.py` is newly authored audit code and imports no supplied checker. It uses the declared 24 monomials `s^a x^b u^c i^e`, with index `a+2b+6c+12e`, and builds its own multiplication table by recursive integer reduction using

```
s^2 = 5
x^3 = 5s x^2 + (100-20s)x + 500-200s
u^2 = 10 + 2s
i^2 = -1.
```

Serialized denominators are positive integers. A separate strict recursive schema pass inspected 183 scalar objects in SOS14, 1,200 in EXACT_KERNELS, 84 in EXACT_SOS_CANDIDATE, and 57 in POSITIVITY_CERTIFICATE, rejecting numeric floats and booleans as integer encodings. All 1,524 objects satisfied the stated scalar schema.

The supplied checker instead uses a cyclotomic/cubic basis. Inspection found its cyclotomic reduction signs correct for `z^8-z^6+z^4-z^2+1`, and its cubic reduction matches the displayed relation. The independent tower computation verified `z=(u+i(s-1))/4`, `z^5=i`, `z^10=-1`, `z^20=1`, the cyclotomic polynomial, the reverse formulas for s and u, and the target sextic at `mu=x/5`, all exactly.

Irreducibility is unnecessary for soundness of a verified zero: the actual selected numbers satisfy each reduction relation, so evaluation from the presented quotient algebra to the actual complex numbers is an algebra homomorphism. A quotient presentation with extra linear dependencies could make a zero test incomplete, but cannot turn a polynomial reduced to zero into a nonzero actual value. The checkers do not invert a general algebraic coefficient. Their arithmetic divisions are positive integer/rational denominator normalizations.

The actual branch is fixed independently of the quotient: `p(3)<0<p(3.1)` and, for every t≥3, `p'(t)=t^3(30t^2-260)+288t+96>0`. Thus the selected root is unique in that range and no larger real root exists. Both A(t)=5(t^3-4t-4) and B(t)=5t^2-4t-8 are positive there; `A(mu)^2=5B(mu)^2` selects `A(mu)=sqrt(5)B(mu)` with positive sqrt(5), which gives the cubic used in reduction. Positive s and u give a unit-modulus z with z^5=i, positive imaginary part and real part >1/sqrt(2), selecting exp(i*pi/10). I checked this reasoning rather than trusting the numerical root label in JSON.

As a distinct numerical arithmetic probe, Decimal precision 160 and independent bisection of p on (3,3.1) evaluated all 576 basis products in the actual embedding. The largest absolute discrepancy was approximately `3.9780201997476e-140`; this is a spot-check, not a substitute for the preceding algebra argument. Direct actual-embedding evaluation gives the smallest weight approximately `0.0003584887345104111936479403159317`.

### Word algebra and SOS orientation

The word algebra is the group algebra of `(C5*C5) × (C5*C5)`: the first free product contains U0,U2 and the second U1,U3. The new reducer represents a word as a pair of reduced syllable lists. It keeps each party's original relative order, merging only adjacent powers of the same generator and removing fifth powers. Reduced free-product normal form is unique; no same-party commutation relation is added.

Explicit attacks confirmed U0 U2 ≠ U2 U0 and U1 U3 ≠ U3 U1 in this reducer, cancellation after cross-party separation, and cancellation exposed by removing adjacent inverse syllables. All 6,561 ordered pairs from Q also passed star-reversal and inverse consistency checks. Those tests support implementation correctness; the normal-form structural argument supplies the reason reduction is valid universally.

For `R=sum a_w w`, the new expansion uses `conj(a_w)a_v w†v` for R†R and `a_w conj(a_v) wv†` for RR†. The full compact certificate has 164 serialized polynomial coefficients and produces 273 word positions. Every position agrees exactly with `mu I-B` in the new tower arithmetic.

The Gram path was separately recomputed using the same new arithmetic: E H E† has coefficients x_ij for q_i†q_j, while the reversed contribution uses conj(x_ij) for q_i q_j†. This agrees with the two positive Gram expressions. The new code checked all 1,681 distinct q_i†q_j words. It explicitly checked that every target word, compact-SOS word and Gram write lies in this universe, addressing the attack that the supplied Gram checker could omit a residual outside its iteration set. No omitted support was found. All 1,681 residuals were exactly zero.

### Positive weights and Gram blocks

The new code verifies the rational interval endpoint conditions for mu, positive sqrt(5), and positive u, then evaluates the real tower monomials directly with rational interval arithmetic. Reality is checked by exact i-conjugation. Every one of the 14 compact weights has a strictly positive rational lower endpoint.

For Gram blocks 1,6,7,8,9, the dimensions are 2,4,3,3,2. The code checks Hermiticity, square dimensions, unit lower-triangular L, and every entry of `H=L D L†`. All 14 D entries are exactly real and have strictly positive rational lower bounds. The rational minima are stored in `independent_results.json`; the displayed decimal is not the positivity decision. The supplied cyclotomic interval implementation was also inspected: it performs correct endpoint products/scales, encloses complex powers of the actual z, and requires a positive real lower endpoint after an exact conjugation check. The imaginary interval contains zero; it is not used to establish reality by tolerance.

These checks close the load-bearing algebra attack: a correctly expanded identity with positive real weights is positive for all bounded unitary representations with the prescribed cross-party commutation, independent of Hilbert-space dimension. Matrix sampling is not needed for that implication.

## Reproducible finding

**ALG-01 — low severity, verifier input-schema robustness; not a C001 proof error.** `verify_independent.py:load_scalar` applies `int()` to each n entry and d without checking the JSON value is an integer or an integer string. A numeric JSON literal 0.5 in an n slot is silently decoded as 0. This permits malformed input outside the stated scalar encoding to receive a successful verifier result.

Reproduction: `audit_attacks.py` copies SOS14 into `mutants/nonintegral_n_accepted/SOS14.json`, changes `terms[0].polynomial[4].coefficient.n[1]` from the integer string `"0"` to the numeric literal `0.5`, and invokes the supplied SOS checker against that copied root. The recorded status is PASS. The original frozen bytes are not altered. The corresponding trace is in `attack_results.json` and `attacks.log`.

Load-bearing path assessed: input decoding → interpreted scalar → expanded identity. The malformed literal is actually interpreted as the original zero coefficient. It therefore does not establish a false upper bound, and does not impair the supplied C001 result: the independent strict scan confirms all 1,524 original scalar encodings satisfy the integer schema. The certificate's stated mathematical domain excludes this malformed input. The rebuttal that `int(0.5)` merely restores the original valid certificate is correct and was checked. If these scripts are advertised as validators of arbitrary JSON certificate syntax, strict integer-type/string validation would be an appropriate hardening change. No scientific repair is required to close this issue for the frozen original inputs.

I found no established counterexample, load-bearing proof error, or specific unresolved algebra gap in the inspected upper-bound path. ALG-01 should not be promoted to a rejection of the theorem.

## Failed substantive attacks and negative controls

The following distinct attacks were executed against receipt-local mutant copies or transient in-memory checker targets. All eleven were rejected, with diagnostics preserved in `attack_results.json`:

| Attack | Observed rejection |
| --- | --- |
| Add 1 to a polynomial coefficient | exact polynomial residual |
| Negate a positive weight | weight not certified positive |
| Add i to a weight | weight not exactly real |
| Remove one anticommutator | wrong anticommutator count |
| Give mu the interval [2,3] | largest-root branch not isolated |
| Give sqrt(5) a negative interval | positive square-root branch not enclosed |
| Relabel one Alice generator 0→2 | duplicate polynomial words |
| Add 1 to a Gram diagonal entry | exact Bell SOS word residual |
| Change a unit L diagonal entry to 2 | L not unit lower triangular |
| Replace direct-check target mu by 2 | exact polynomial residual |
| Replace Gram-check target mu by 2 | nonzero identity-word residual |

The last two deliberately seek a universally false upper bound: the supplied attaining strategy gives >3. They demonstrate that both checked paths bind the identity coefficient to the claimed bound in these controls. Mutation rejection alone does not prove general soundness; the new exact expansion and embedding analysis address that broader question.

An additional independent representation probe constructed random fifth-order PVM unitaries via QR, lifted Alice and Bob to tensor products, and multiplied the original ordered words as matrices without any word reducer. Local dimensions were (2,3), (3,4), (5,5), (5,7), (7,9), and the printed attaining strategy at (5,5). Most random cases have noncommuting measurements on both parties; the first (2,3) case happens to have commuting Alice measurements and noncommuting Bob measurements. The largest matrix SOS residual was `5.329522249959877e-15`. In the attaining strategy the commutator norms on both sides are about 2.8284, the eigenvector residual was `3.4631840863030053e-16`, and the direct Bell expectation was `3.0157104755226722`. This tests the SOS orientations in genuine noncommuting representations. Its floating-point nature limits it to falsification/supporting evidence.

## Original supplied replays and reproduction

All three supplied checkers were read before execution. Their original-candidate logs are `supplied_sos.log`, `supplied_independent.log`, and `supplied_statement.log`, with corresponding JSON result files. They ran successfully, including physical checks. These are original-candidate replays, kept separate from the new arithmetic in `audit_exact.py` and the attacks in `audit_attacks.py`; no printed PASS was treated as a mathematical argument.

From this receipt directory, portable replay commands are:

```
python audit_exact.py --input-dir ../../audit_view
python audit_attacks.py --input-dir ../../audit_view
```

The runtime used was the provided bundled Python executable; `audit_exact.py` needs only the standard library. `audit_attacks.py` additionally uses the already available NumPy for matrix probes. Both accept `--output-dir`, default to this script directory, and resolve their default input directory relative to the script. Actual executed stdout/stderr is preserved as `independent_exact.log` and `attacks.log`. Mutation JSONs are deliberately retained to make ALG-01 and rejection controls adjudicable.

## Limits and disposition

This is a bounded adversarial audit of the algebra in the exact supplied view. The new exact computation uses a different basis from the supplied final checkers, but the square-root tower is described in the proof and was used in discovery; the mathematical generating relations necessarily overlap. It is a separate implementation, not independent discovery of the certificate. The group normal-form algorithm implements the same justified abstract normal form, with a different representation. No claim of external formalization, proof assistant verification, language/runtime verification, maximal mutant coverage, or exhaustive search for quantum strategies is made.

The full-source correspondence outside this view, discovery provenance, literature novelty and publication framing were not examined. I did not independently reproduce the supplied full exact 25-coordinate physical calculation in a second symbolic matrix engine; I inspected its source and ran it, then supplied a direct numerical Fourier-projector reconstruction. The target of this subaudit was the universal upper-bound algebra, for which the new full exact identities and rational positivity checks supply independent evidence. The physical and POVM statement questions remain within the other assigned audit scope.

The strongest attempted fatal-flaw paths—wrong actual embedding, hidden same-party commutation, reversed SOS coefficients, unchecked support, and failed strict positivity—were attacked in this run and closed for the original hashes. No actionable unresolved algebra fatal-flaw test is being handed off. ALG-01 is the sole established implementation weakness found and has the limited disposition described above.

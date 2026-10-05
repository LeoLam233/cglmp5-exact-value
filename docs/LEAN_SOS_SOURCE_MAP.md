# Compact SOS and reflection source map

Status: the actual `CGLMP5.SOS.compact_identity` compiled successfully on 2026-10-04, with all 273 normal-word residuals and 6552 exact integer coordinate equalities. This document records development source alignment. It is not a fresh independent kernel replay or one of the three mandatory final audit rounds.

## 1. The public theorem and its represented objects

`lean/CGLMP5/SOSIdentity.lean` exports `CGLMP5.SOS.compact_identity` for an arbitrary complex star algebra `R`, with `Ring`, `StarRing`, `Algebra ℂ`, and compatible `StarModule ℂ` structure. It quantifies over `a b : Fin 2 → unitary R`, assumes each generator has fifth power one, and assumes only cross-party commutation `∀ i j, Commute (a i) (b j)`.

The conclusion is exactly

```
(mu : ℂ) • (1 : R) - SOS.bell (zeta ^ 4) a b =
  ∑ j : Fin 14, (weightValue j : ℂ) •
    (star (SOS.realizingPolynomial a b j) * SOS.realizingPolynomial a b j +
      SOS.realizingPolynomial a b j * star (SOS.realizingPolynomial a b j))
```

There are no scalar-table, certificate-validity, numerical residual, finite-dimensionality, same-party commutativity, or state-vector premises in this public theorem. The algebraic theorem specializes to bounded operators; positivity and universal POVM transfer are separate analytic steps.

The constant `mu` is the actual real root from `Root.lean`, with the literal sextic equation and largest-real-root theorem. `zeta` is the actual complex embedding identified with its exponential branch. The theorem does not use an unspecified quotient-ring root.

`SOS.realizingPolynomial` in `SOSRealization.lean` evaluates `CanonicalData.polynomial j` directly, mapping each exact scalar through `Scalar.eval`. It is not a separately selected polynomial optimized only for a particular state. `weightValue j` is `Scalar.evalReal (CanonicalData.weight j)`; `weight_evaluation` identifies its complex cast with the exact scalar evaluation. `weight_positive` and the stronger `weight_gt_one_div_three_thousand` prove positivity for all 14 weights.

## 2. Link to the frozen compact source

The source is `artifact_v0.1.1/SOS14.json`, SHA256 `1c0708628ca5b89caef11a80d3a5e89f4074a14a26ea5c2d2d92087ffa5f22c2`.

The literal typed records are `CertificateSource.rawTerms` in `CertificateData.lean`. `CanonicalData.rawTerm` selects those same records, and `CanonicalData.weight` / `CanonicalData.polynomial` decode their integer numerator vectors and positive denominators. `rawTerms_valid` and `rawTerm_valid` prove the dimensions, denominator positivity, and generator-label validity used by these decoders. The syntactic default-zero array access in `decodeScalar` is covered by exact length-24 validity; it is not a repair for missing source data.

`CertificateSource.canonical_source_decode` and `canonical_text_decode` in `CertificateSource.lean` prove that the chunked decimal encoding and the uninterrupted decimal-string decoding yield those same `rawTerms`. The full rendered-source byte comparison is a separately executed provenance gate, implemented by `scripts/check_lean_source_bytes.py`; the documentation does not portray a Python hash annotation as a Lean theorem. Header and embedding/gamma linkage are covered by the source-provenance modules and the master `SOURCE_MAP.md`.

The SOS identity depends directly on the concrete decoded records. The source-decoding theorem establishes the provenance of those records; it does not add a hypothesis to the SOS identity. Both proof surfaces are checked in the final whole-production validation.

## 3. Ordered noncommutative semantics

`WordSyntax.lean` keeps two ordered local factor lists. `PartyWord.push` reduces exponents modulo five and combines only adjacent occurrences of the same local generator. `PartyWord.reduce` never sorts local generators. Adjoint reverses the order and negates exponents modulo five.

`Words.lean` proves evaluation of reduction, multiplication, and adjoint. In particular, `Word.evalStar_mul` uses order-five relations and cross-party commutation, and `Word.evalStar_adjoint` identifies the formal adjoint with the represented star operation. Neither theorem grants commutation between the two Alice generators or between the two Bob generators.

`CertificateSource.rawCoefficient_eval` in `SourceWordBridge.lean` connects the literal ordered source-generator product to separated-party `Word.evalStar`. Its labels are explicitly `0=A0`, `1=B0`, `2=A1`, `3=B1`; party separation is justified by cross-party commutation and source-label validity.

## 4. Target Bell expression

`SOSDefinitions.lean` defines all sixteen nonconstant Fourier terms explicitly. `fourierCoeff` uses the finite Fourier sum of `1-z/2`; `edgeCoefficient` includes the last cyclic edge's extra `omega^(-k)` factor. `edgeWord` preserves the specified order and setting assignment. `SOS.bell (zeta^4)` is therefore a concrete expression, not an uninterpreted Bell-operator variable.

`SOSFinite.target_evaluation` in `SOSTarget.lean` evaluates the literal 17-term target polynomial as `(mu : ℂ) • 1 - SOS.bell (zeta^4) a b`. `SOSFinite.target_index_word_map` and `target_index_coefficients` check its correspondence with the indexed target table. The literal event-functional/Fourier bridge is proved separately by `CGLMP5.sosBell_eq_literal`, so a scaled or relabelled inequality cannot be substituted silently.

## 5. Exact compression and expansion witnesses

The 164 canonical polynomial coefficients are represented through 28 actual source-selected phase cores and 20 exact powers of the twentieth root. There are 135 ordered weighted core pairs. This compression reduces arithmetic cost; it does not introduce assumed symmetries.

- `SOSCompressedCheck00` through `13` check every source-coefficient phase expression, every conjugated ordered core product, and every weighted core product.
- `SOSFinite.phasePolynomial_eq_canonical` in `SOSPhaseLink.lean` proves the compressed phase polynomial equals each actual `CanonicalData.polynomial` after scalar evaluation.
- `SOSPhaseBaseChecks` and the 20 `SOSPhasePairNN` modules check the phase identities. `SOSFinite.phase_pair_check` in `SOSPhaseChecks.lean` assembles them without re-evaluating their numeric leaves.
- `SOSExpansion00` through `13` check the ordered word expansion, including both `R*R` and `RR*` contributions. Their aggregate is `feature_expansion_checked`.
- `SOSIndexFiber000` through `272` check that each indexed coefficient fiber equals the corresponding filtered expansion. Their aggregate is `index_fiber_checked`.

The expansion contains 4320 ordered contributions and 273 normal-word indices. No injectivity premise for the index-to-word map is needed: summing by an index is valid even if two represented words coincide.

`SOSFinite.reflected_sos_evaluation` in `SOSSemantics.lean` uses the actual scalar multiplication theorem, actual source/phase/core witnesses, and generic word evaluation to evaluate the complete reflected polynomial as the fourteen canonical weighted anticommutators. All intermediate conditional semantic helpers are instantiated here.

## 6. Integer residuals and reflection

`SOSIntegerDataSoundness` identifies every literal numerator/denominator record with the exact scalar used by the compressed polynomial or target. `Scalar.mul_ofCanonical` and the common-denominator lemmas prove the conversion from rational tower arithmetic to integer arithmetic.

For each word index, `SOSIntegerResidualNNN` proves denominator divisibility and all 24 integer coordinate equalities. The proof uses:

1. kernel-checked exact denominator quotient witnesses;
2. opaque literal lookup equalities, whose bodies are reflexive proofs;
3. universally proved sparse phase-action formulas from `SOSPhaseLinear00` through `19`;
4. final integer equality checks through `decide +kernel`.

No native decision procedure or external arithmetic result is admitted as a proof. Python emits candidate literals and proof statements; Lean checks every numerical equality. `SOSFinite.integer_residual` in `SOSIntegerResidualChecks.lean` assembles all 273 families through the checked `Fin.cases` eliminator.

`SOSFinite.fiberValue_eq_target_of_integer` in `SOSIntegerSemantics.lean` proves that the checked integer cross-products imply exact rational coefficient equality. `SOSReflectionCore` proves the generic coefficient-collection argument. The thin `SOSReflection` module instantiates it with the actual denominator, residual, fiber, and target theorems, yielding `reflected_evaluation_eq_target` with no certificate assumptions.

Finally, `SOS.compact_identity` in `SOSIdentity.lean` is a three-step equality chain: target evaluation, reflected coefficient equality, and actual anticommutator evaluation.

## 7. Reproduction and scope of this coverage

The active generators support read-only reproducibility checks:

```
python scripts/generate_lean_sos_arithmetic.py --check
python scripts/generate_lean_sos_phase_checks.py --check
python scripts/generate_lean_sos_residual_stages.py --check
```

All three matched the checked production sources during development. The successful but superseded All272 fallback and earlier failed prototypes were preserved outside production. Every remaining production Lean module is subject to the whole-tree build policy, including any module not reachable from the default root.

The final release additionally requires the actual bounded-operator identity and tensor-POVM upper theorem, physical attainment, supremum/maximality assembly, clean whole-production compilation, independent fresh kernel replay, frozen source/mutation gates, and the three prescribed audit rounds. This map alone does not certify those separate completion gates.

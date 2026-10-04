# Final bounded cross-interface review

Verdict: **PASS; no edit required**.

Reviewed at 2026-10-04 10:15 UTC: hardened `verification_receipt.py` and
`strict_schema.py`, manuscript `main.tex` convention/theorem/embedding/bridge
and attainment equations, and `docs/LEAN_HANDOFF.md` canonical source map.
This is a consistency review of those interfaces, not a new proof engine or a
claim that later publication steps have completed.

1. **Target and quantifiers.** Receipt target ID describes the standard
   five-outcome, two-setting, local-bound-2 problem. The manuscript explicitly
   asserts I5 <= mu for every admissible strategy and takes the supremum over
   all local Hilbert spaces/states/POVMs; equality is attained on C^5 tensor C^5.
   The Lean map says the same. No source asserts equality for every fixed
   dimension, confuses dimension with outcome count, or weakens the universal
   upper bound to Fourier/projective/five-dimensional strategies.
2. **Event convention.** The four positive and four negative receipt event
   strings match manuscript equation eq:cglmp term by term, with k=0,1 and
   weights 1-k/2. The Lean map points to those literal events and retains the
   shifts D0=A0, D1=B0, D2=A1+1, D3=B1+1 and the wraparound subtraction of one.
   The Fourier sum and omega^(-k) wrap phase agree with the verifier target.
3. **Polynomial/root.** Receipt descending coefficient vector
   [5,0,-65,0,144,96,16] is exactly manuscript/Lean-map p(t). The unique root
   above3 agrees with the largest real root, using p(3)<0 and positive p' on
   [3,infinity). The cubic in x=5mu is unchanged.
4. **Scalar interpretation.** All three interfaces use the same index
   a+2b+6c+12e, x=5mu, positive s=sqrt5 and u=sqrt(10+2s), and positive i;
   zeta=(u+i(s-1))/4=exp(i*pi/10). Formal ring reduction and actual root/sign
   selection are separate. No irreducibility or unproved denominator
   inversion is silently assumed.
5. **POVM and state model.** The receipt names the fixed-J bridge; manuscript
   and Lean map explicitly distinguish bounded commuting PVM upper bounds
   from the local tensor-product POVM theorem. One fixed J per party handles
   both settings with complement completion. The manuscript's self-adjoint
   Halmos block W and the artifact note's W:H+M -> M+H differ only by swapping
   output summands: their conjugated projectors and compressions coincide.
   Mixed/nonnormal states and infinite/nonseparable spaces are covered without
   a multiplicative-compression premise.
6. **Physical attainment.** Lean map and manuscript use the same offsets
   (0,1/2) and (1/4,-1/4), palindromic Schmidt coefficients (1,a,b,a,1), positive
   denominator greater than4, and full25-dimensional eigenvector check.
   Receipt checked-claim scopes correctly distinguish full physical PASS,
   upper-bound-only PASS, statement consistency and schema-only PASS.
7. **Canonical data and later formalization.** The four Lean-map hashes are
   the exact byte-identical v0.1/v0.1.1 mathematical data hashes independently
   checked here. Compact/Gram universes273/1681 and14 weights are consistent;
   164 stored records are all nonzero only for the fixed baseline. Current
   canonical-policy variants retain the distinction. The source map explicitly
   begins only from a future remotely verified v0.1.1 tag and reserves actual
   Lean formalization for a separate task/v0.2.0; no formal result is claimed.

Final frozen manuscript recheck at 10:18 UTC: the printed-data parser passed again,
and the convention/theorem/root/basis/bridge equations were reread unchanged in
substance. Final main.tex SHA-256: `3284a967e877b0235fe3bb33ee7836578a4196e3457d54740550c392432b4673`.
All five data-table files are unchanged. Initial review receipts are retained in
`printed_review_initial/`.

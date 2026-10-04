# One fixed local embedding for both measurement settings

The exact SOS identity gives a positive bounded operator in every representation
of the unitary and cross-party commutation relations. This note makes explicit
the extension from local projective measurements to local five-outcome POVMs.
There is no finite-dimensional restriction, injectivity assumption on an effect,
or multiplicativity assumption on compression.

## Simultaneous common-space construction

Let H be any complex Hilbert space and let
`E[a|x] >= 0`, `sum_a E[a|x] = I_H`, for `a=0,...,4` and `x=0,1`.
Put `M = H ⊗ C^5` and, for each setting, define the isometry

\[
 V_x h=\sum_{a=0}^4 E_{a|x}^{1/2}h\otimes |a\rangle,
 \qquad V_x^*V_x=I_H.
\]

Square roots exist for bounded positive operators; the identity follows from
POVM completeness. Let `Q_a = I_H ⊗ |a><a|` and
`D_x = I_M - V_x V_x^*`. D_x is an orthogonal projection and `D_x V_x=0`.
The explicitly given operator

\[
 W_x:H\oplus M\longrightarrow M\oplus H,\qquad
 W_x(h,k)=(V_xh+D_xk,\,V_x^*k)
\]

is unitary: its adjoint is
`W_x^*(l,g)=(V_x^*l,D_x l+V_x g)`, and multiplication in either order gives
the identity, using `D_x^2=D_x`, `D_x V_x=0`, and `V_x^*V_x=I`.
This formula does not assume that unrelated infinite-dimensional complements
are isomorphic.

On the **same space K = H ⊕ M for both x**, use the **same isometry**

\[
 J:H\to K,\qquad Jh=(h,0).
\]

Define

\[
 P_{a|x}=W_x^*(Q_a\oplus\delta_{a0} I_H)W_x.
\]

For each x these are five pairwise orthogonal projections summing to `I_K`.
The summand `delta[a,0] I_H` completes the unused complement. Since
`W_x Jh=(V_xh,0)`,

\[
 J^*P_{a|x}J=V_x^*Q_a V_x=E_{a|x}
\]

for **both settings with precisely the same J**. Zero effects, rank-deficient
effects, finite or infinite rank, and nonseparable H are all allowed.

Equivalently, one can identify each setting's minimal dilation space as
`H ⊕ K_x`, place them in `H ⊕ K_0 ⊕ K_1`, and assign every unused summand to
outcome 0. This gives the same common-embedding principle. The explicit defect
formula above avoids relying on an unstated unitary-extension theorem.

## Bipartite preservation, including mixed states

Perform this construction separately for Alice and Bob, with fixed `J_A,J_B`
and extended spaces `K_A,K_B`. For every pair of outcomes and settings,

\[
 (J_A\otimes J_B)^*
 (P^A_{a|x}\otimes P^B_{b|y})
 (J_A\otimes J_B)
 =E^A_{a|x}\otimes E^B_{b|y}.
\]

This identity is tensor-factor compression. It does **not** assert
`J^*XYJ=(J^*XJ)(J^*YJ)` for two same-party operators.
For a density operator rho on the original bipartite space, use the single
extended state `(J_A ⊗ J_B) rho (J_A ⊗ J_B)^*`; it is positive with trace one
and preserves every joint probability. Neither the state nor the embedding
may depend on the measurement setting. Unequal local dimensions cause no issue.

More generally any normalized positive functional phi on the original bounded
operators, including a nonnormal state, extends to
`phi_tilde(T)=phi(J_AB^* T J_AB)`, since compression is unital and positive.
It gives exactly the same joint expectations. No density operator representation
or trace-class assumption is required for this formulation.

## Transfer of the exact upper bound

The dilated five-outcome projective measurements yield bounded order-five
unitaries. Operators on opposite tensor factors commute, so the same SOS
identity is valid after substitution. Its weights are positive in the fixed
actual scalar embedding and each `R*R+RR*` is positive. Therefore
`mu I - B >= 0` on the enlarged space. Positive-state evaluation or compression
proves the original POVM bound, with all joint probabilities unchanged.
No finite-dimensional approximation or limit exchange occurs.

The SOS also directly covers arbitrary bounded commuting **projective**
representations. The local-POVM theorem here concerns bipartite tensor-product
models; it does not silently claim that separate local dilation preserves an
arbitrary previously specified non-tensor commuting-algebra structure.

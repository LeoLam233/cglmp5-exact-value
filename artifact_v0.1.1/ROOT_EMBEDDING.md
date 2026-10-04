# Real embedding and exact root selection

This note is part of the proof, not a numerical root guess.

Let

\[
p(t)=5t^6-65t^4+144t^2+96t+16.
\]

We have \(p(3)=-20<0<p(31/10)\). For \(t\ge3\),

\[
p'(t)=t^3(30t^2-260)+288t+96>0.
\]

Thus there is exactly one root \(\mu\) in \((3,31/10)\), and there are no roots
larger than it: it is the largest real root of the specified sextic. The
certificate encloses it with rational endpoints obtained by bisection; the
independent checker checks both endpoint signs again.

Set

\[
A(t)=5(t^3-4t-4),\qquad B(t)=5t^2-4t-8.
\]

Direct polynomial multiplication gives

\[
A(t)^2-5B(t)^2=5p(t).
\]

For \(t\ge3\), both \(A(t)>0\) and \(B(t)>0\): their values at 3 are positive
and their derivatives are positive in this range. Consequently
\(A(\mu)/B(\mu)=+\sqrt5\), not the negative branch. Writing \(s=+\sqrt5\) yields

\[
\mu^3=s\mu^2+(4-4s/5)\mu+4-8s/5.
\]

With \(x=5\mu\), this is exactly

\[
x^3=5sx^2+(100-20s)x+500-200s.
\]

Next take \(u=+\sqrt{10+2s}\) and

\[
\zeta=\frac{u+i(s-1)}4.
\]

Its modulus is one, its imaginary part is positive, and its real part is
larger than \(1/\sqrt2\). Exact multiplication using \(s^2=5\) and
\(u^2=10+2s\) gives \(\zeta^5=i\). Among the solutions of this equation,
these sign and real-part conditions select \(\zeta=e^{i\pi/10}\).
In particular \(\omega=\zeta^4=e^{2\pi i/5}\).

The first arithmetic implementation uses the 24 spanning monomials
\(s^a x^b u^c i^d\), with \(a,c,d\in\{0,1\}\), \(b\in\{0,1,2\}\).
The independent implementation uses \(\zeta^a x^b\), \(0\le a<8\),
\(0\le b<3\), reducing by

\[
\Phi_{20}(z)=z^8-z^6+z^4-z^2+1,
\quad s=2(z^2+z^{-2})-1,\quad u=2(z+z^{-1}),\quad i=z^5.
\]

**Irreducibility of either displayed presentation is not needed for the
certificate.** Every exact zero checked by reduction is a polynomial
identity modulo relations obeyed by the specified actual complex numbers.
All serialized coefficients have a strictly positive integer denominator;
the final check introduces no division by an unverified algebraic quantity.
The discovery algorithm used divisions, but their identities were checked
and the final verifier only adds and multiplies the serialized coefficients.

For positivity, the primary implementation evaluates the real tower basis
on rational enclosures for \(\mu,s,u\). The independent checker instead
converts each coefficient into the cyclotomic/cubic basis, propagates real
and imaginary rational intervals for powers of
\(\zeta=(u+i(s-1))/4\), and recomputes the pivot bounds. Both require strictly
positive rational lower endpoints. No floating-point eigensolver or guessed
root label is an input to either positivity verdict.

## v0.1.1 clarification: formal ring versus actual positive embedding

The exact calculation first takes place over the presented rational coefficient
ring

\[
 \mathbb Q[s,x,u,i]/(s^2-5,\;x^3-5sx^2-(100-20s)x-500+200s,
                    \;u^2-10-2s,\;i^2+1).
\]

The cyclotomic implementation uses the compatible presentation with
`Phi_20(z)=0`, `s=2(z^2+z^-2)-1`, and the same cubic for x. The selected actual
numbers define a homomorphism into the complex numbers. Therefore a formal
zero produced by reduction evaluates to zero. This implication needs neither
irreducibility, a field claim, nor injectivity of that evaluation map.
Conversely, equality at one embedding is not asserted to imply formal equality.

Positivity is a separate assertion **after** evaluation at
`s=+sqrt(5)`, `u=+sqrt(10+2s)`, `x=5*mu` with `mu>3`, and the specified i.
The rational boxes rigorously enclose those actual numbers. The verifier first
checks exact reality by conjugation and then a strictly positive rational lower
endpoint. A compatible conjugate embedding still preserves any formal identity,
but need not preserve the positive weights or the Bell/measurement convention.
In particular a formal identity by itself is not a positive SOS upper bound.

Valid broader boxes are permitted if all branch and strict positivity tests
still succeed. The exact frozen narrow endpoints are not mathematical axioms.
The schema and receipts identify the enforced basis and branch separately from
historical descriptive fields; see `SCHEMA.md`.

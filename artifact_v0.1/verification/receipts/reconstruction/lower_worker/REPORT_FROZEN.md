# Unguided reconstruction receipt: attainable C001 lower bound

Outcome: **PARTIAL**. A five-dimensional pure state and local rank-one projective measurements attain exactly the exposed target \(\mu\), the largest real root of \(5t^6-65t^4+144t^2+96t+16\). Thus this worker has established \(\sup I_5\geq\mu\). This receipt contains no universal upper bound over other states, POVMs, measurements, or Hilbert-space dimensions. It does not reconstruct the full claimed supremum theorem.

This unguided report was frozen on 2026-10-03 at 18:42:53 UTC, after the computation had passed. No method-only hint was requested or received. The supplied root/polynomial is target exposure, and is not being presented as an independently discovered numerical conjecture.

## Actual input and exposure

The only workspace input read was the full text of <LOCAL_POST_VERIFICATION>/reconstruction_view/TARGET.md. Its bytewise SHA-256 is:

    0480e476fde75b9cdc540066ad1bcfc36f2f6375a04afbf848396f24bdc5b61d

TARGET.exposed.md is a byte-for-byte copy of that exposure, included for portable replay. Other exposures were the parent assignment, the Python runtime path, the environment/cwd information, and a parent reminder to use portable receipts and label a lower bound PARTIAL. No candidate proof, witness, SOS certificate, discovery code, audit file, PASS summary, project memory, other workspace input, other agent result, mathematical reference page, or source from the internet was read. General mathematical reasoning and internal familiarity with Fourier bases were used; no solution-specific black box was invoked. One brief procedural commentary was emitted before reading the boundary file. No tool sent messages to users or external recipients, and nothing was published.

## Deriving a concrete Fourier strategy

The cyclic equality predicates suggest trying Fourier bases on a five-dimensional local space, with opposite output signs for the two parties. This is a construction ansatz, with no claim that all POVMs can be reduced to it.

For outputs \(a,b=0,\ldots,4\), define

\[
 |a;x\rangle={1\over\sqrt5}\sum_{j=0}^4
 \exp\!\left({2\pi i j(a+\alpha_x)\over5}\right)|j\rangle,\qquad
 |b;y\rangle={1\over\sqrt5}\sum_{j=0}^4
 \exp\!\left({2\pi i j(-b+\beta_y)\over5}\right)|j\rangle.
\]

Each measurement is the set of the five projectors onto these vectors. Within a fixed setting, inner products for unequal outputs are sums of distinct fifth roots of unity, hence zero; diagonal inner products equal one. Therefore the projectors are positive, orthogonal, sum to the identity, and are admissible five-outcome POVMs. Naimark dilation is not needed.

For a real normalized vector \(\eta\) and state \(\sum_j\eta_j|jj\rangle\), put \(\delta_{xy}=\alpha_x+\beta_y\). The Born rule gives

\[
 P(A_x=B_y+r)={1\over5}\left|\sum_j\eta_j
 e^{-2\pi i j(r+\delta_{xy})/5}\right|^2.
\]

To balance the four positive \(k=0\) arms, choose their effective shifts to be \(q,-q,q,-q\). In the order of the exposed inequality this requires

\[
 \delta_{00}=q,\quad \delta_{10}=1-q,\quad
 \delta_{11}=q,\quad \delta_{01}=-q.
\]

The additive phase relation \(\delta_{00}+\delta_{11}=\delta_{10}+\delta_{01}\) now forces \(q=1/4\). Fixing the harmless phase gauge \(\alpha_0=0\) gives the explicit phases

\[
 (\alpha_0,\alpha_1)=(0,1/2),\qquad
 (\beta_0,\beta_1)=(1/4,-1/4).
\]

The four positive arms at general \(k\) then have shifts \(+(k+1/4),-(k+1/4),+(k+1/4),-(k+1/4)\). The four negative arms have shifts \(-(k+3/4),+(k+3/4),-(k+3/4),+(k+3/4)\). The modulus squared is even in the shift for real \(\eta\). Expanding it gives \(I_5=\eta^T T\eta\), where

\[
 T_{jj}=0,\qquad
 T_{j\ell}={4\over5}\sum_{k=0}^1(1-k/2)
 \left[\cos{2\pi(j-\ell)(k+1/4)\over5}
       -\cos{2\pi(j-\ell)(k+3/4)\over5}\right].
\]

Elementary root-of-unity/trigonometric arithmetic reduces the four distinct off-diagonal coefficients to

\[
 c_r={1\over2\cos(\pi r/10)},\quad r=1,2,3,4.
\]

In exact radicals, with \(s=\sqrt5\),

\[
 u=c_1=\sqrt{(5-s)/10},\quad v=c_2=(s-1)/2,\quad
 w=c_3=\sqrt{(5+s)/10},\quad z=c_4=(s+1)/2.
\]

These values follow, for example, from the positive roots for \(2\cos(\pi/5)\), \(2\cos(2\pi/5)\), and the half-angle identity; they can also be obtained by fifth/tenth-root polynomial arithmetic. In particular \(uw=s/5\), \(vz=1\), and \(w=zu\). The real restriction is

\[
 T=\begin{pmatrix}
 0&u&v&w&z\\
 u&0&u&v&w\\
 v&u&0&u&v\\
 w&v&u&0&u\\
 z&w&v&u&0
 \end{pmatrix}.
\]

## Exact characteristic polynomial and eigenvector

Reflection \(j\mapsto4-j\) commutes with \(T\). On the normalized symmetric basis
\((e_0+e_4)/\sqrt2,(e_1+e_3)/\sqrt2,e_2\), the restriction is

\[
 S=\begin{pmatrix}
 z&u+w&\sqrt2v\\
 u+w&v&\sqrt2u\\
 \sqrt2v&\sqrt2u&0
 \end{pmatrix}.
\]

Direct determinant expansion, checked with exact rational arithmetic in \(\mathbb Q(s)\), gives

\[
 f_s(t)=\det(tI-S)
 =t^3-st^2+(-4+4s/5)t-4+8s/5.
\]

The antisymmetric restriction is
\(\begin{pmatrix}-z&u-w\\u-w&-v\end{pmatrix}\), with characteristic polynomial \(g_s(t)=t^2+st+2s/5\). Thus the exact characteristic polynomial of the five-dimensional restriction is \(f_s(t)g_s(t)\). The exposed sextic is not the characteristic polynomial of this five-dimensional matrix. It is the rational field norm of the cubic:

\[
 5f_s(t)f_{-s}(t)=5t^6-65t^4+144t^2+96t+16.
\]

For an indeterminate \(t\), define

\[
 D=t^2-vt-2u^2,\quad
 E=t(u+w)+2uv,\quad
 F=2v(t-v)+2u(u+w).
\]

The row equations satisfy the exact polynomial identity

\[
 (tI-T)(D,E,F,E,D)^T=(f_s(t),0,0,0,f_s(t))^T.
\]

The script verifies the three distinct row residuals coefficient by coefficient in \(\mathbb Q(s)[t]\); it represents \(E=u((3+s)t/2+2v)\), so no approximate radical simplification is used.

An exact rational Sturm chain for the sextic has variation counts \(1,0,0\) at \(a=301571/100000\), \(b=301572/100000\), and \(+\infty\), respectively. Neither endpoint is a root. Consequently the sextic has exactly one real root in \((a,b)\), and no real root above \(b\). To associate this root to \(f_s\), the script encloses \(\sqrt5\) strictly between

\[
 {2236067977499789\over10^{15}}
 <\sqrt5<
 {2236067977499790\over10^{15}}
\]

by exact squared comparisons, and obtains \(f_s(a)<0<f_s(b)\) using rational interval arithmetic. Continuity therefore gives an \(f_s\)-root in this same interval. The norm identity and Sturm counts identify it as the largest real sextic root \(\mu\). The complete rational chain and endpoint enclosures are in exact_computation.log.

Set \(D,E,F\) at \(t=\mu\). Since \(\mu>3\), \(0<v<1\), and \(0<2u^2<1\), one has \(D>\mu^2-\mu-1>5\). Hence the vector is nonzero. The exact normalized state is

\[
 |\psi\rangle=
 {D(|00\rangle+|44\rangle)+E(|11\rangle+|33\rangle)+F|22\rangle
  \over\sqrt{2D^2+2E^2+F^2}}.
\]

The eigenvector identity now implies \(I_5=\eta^T T\eta=\mu\), proving attainment. Independently computed decimal coefficients are approximately
\((0.53683879888192236,0.38592200127219078,0.35459360667976545,
0.38592200127219078,0.53683879888192236)\), and decimal bisection of the derived cubic yields
\(\mu=3.0157104755226732855239838019610432817\ldots\).

## Executed verification and stopping boundary

Python 3.12.14 on Windows 11 (10.0.26300), with NumPy 2.3.5, executed reconstruct.py successfully. Exact algebra uses only Python standard-library Fraction plus the included elementary \(\mathbb Q(\sqrt5)\) and rational polynomial/Sturm implementation. An initial environment query attempted to import scipy and failed because it was absent; sympy, scipy, and mpmath were subsequently confirmed absent. No package was installed. This caused no mathematical blocker.

The exact determinant coefficients, norm identity, eigenvector polynomial residuals, radical enclosure, root isolation, and absence of larger sextic roots all passed their assertions. Separately, the script constructed all four actual measurement bases, all 100 joint probabilities, every event in the supplied inequality, and the full 25-dimensional Bell operator directly from projectors. It did not use the Toeplitz formula to compute the direct event value.

The direct Born-rule value was 3.015710475522672, within \(1.34\times10^{-15}\) of the independently computed cubic root. The normalized-state error was zero at floating-point precision; the largest basis-unitarity error was \(2.20\times10^{-15}\); probability normalization errors were at most \(3.34\times10^{-16}\). The full Bell-operator eigenvector residual was \(2.02\times10^{-15}\), its leakage out of the diagonal state subspace was \(1.68\times10^{-15}\), and its diagonal restriction agreed with the separate cosine construction to \(3.12\times10^{-15}\). These numerical checks support the exact proof but are not replacements for it.

The attempt used one phase-balancing construction and exact/numerical validation. It stopped once the target was attained and the exact state/root identification was established; no exhaustive phase search or arbitrary computational campaign was run. A universal upper proof remains outside this complementary task and is neither inferred from the fixed-measurement eigenvalue nor claimed. No method-only guidance is needed for the completed lower-bound part.

For replay, run Python with this directory's reconstruct.py; its default input is the included TARGET.exposed.md and its default output is this directory. Optional --input and --output arguments make the paths explicit. The script requires only NumPy beyond the Python standard library. Dependencies and commands are recorded in ENVIRONMENT_AND_COMMANDS.md, numerical checks in checks.json, exact arithmetic receipts in exact_computation.log, and captured stdout in run_stdout.log.

# Unguided elementary closure of two arithmetic steps

This addendum was written after REPORT_FROZEN.md, without consulting any new input or receiving any hint. It supplies elementary proofs of coefficient reduction and largest-root identification, so that neither trigonometric values nor the Sturm root-count rule need be treated as a solution-specific black box. The outcome remains PARTIAL and the full upper bound remains unproved.

For coefficient reduction, let \(\zeta=e^{2\pi i/5}\) and \(v=\zeta+\zeta^{-1}=2\cos(2\pi/5)>0\). Dividing \(1+\zeta+\zeta^2+\zeta^3+\zeta^4=0\) by \(\zeta^2\) shows \(v^2+v-1=0\), hence \(v=(\sqrt5-1)/2\). The half-angle identity and the positive sign give \(2\cos(\pi/5)=z=(\sqrt5+1)/2=v+1\), \(u=1/(2\cos(\pi/10))=\sqrt{(5-\sqrt5)/10}\), and \(w=1/(2\cos(3\pi/10))=\sqrt{(5+\sqrt5)/10}\). In particular
\[
 {u\over w}=v,\qquad {w\over u}=z,\qquad
 5u^2=2-v,\qquad 5w^2=2+z.
\]

The four entries from the finite cosine sum in the frozen report reduce as follows:

| Difference \(r\) | Cosine-sum coefficient before reduction | Reduced value |
|---|---|---|
| 1 | \(2/(5u)-1/(5w)\) | \(u\), since \(5u^2=2-u/w\) |
| 2 | \((2z+3v-2)/5\) | \(v\), since \(z=v+1\) |
| 3 | \(2/(5w)+1/(5u)\) | \(w\), since \(5w^2=2+w/u\) |
| 4 | \((2v+3z+2)/5\) | \(z\), since \(v=z-1\) |

These reductions use only the root-of-unity equation, positivity of the indicated cosines, the elementary double-angle identity, and exact arithmetic.

There is also a short largest-root proof that does not rely on the Sturm rule. Put \(s=\sqrt5\), and write
\[
 f_s(t)=A(t)-sH(t),\quad f_{-s}(t)=A(t)+sH(t),
 \qquad A=t^3-4t-4,\quad H=t^2-4t/5-8/5.
\]
For \(t\geq3\), \(A(3)=11\), \(H(3)=5\), and both \(A\) and \(H\) are increasing because their derivatives are positive. Thus \(f_{-s}(t)>0\) on this entire half-line. Also \(s<9/4\), so
\[
 f_s'(t)=3t^2-2st-4+4s/5
 >3t^2-(9/2)t-4>0\quad(t\geq3).
\]
The last quadratic has value \(19/2>0\) at \(3\) and increases thereafter. Further, \(f_s(3)=11-5s<0\), since \(s>11/5\), and \(f_s(t)\) tends to \(+\infty\). Therefore \(f_s\) has exactly one root above \(3\). The rational endpoint checks in the frozen computation put this root in \((3.01571,3.01572)\).

Finally, the exact identity \(p(t)=5f_s(t)f_{-s}(t)\) implies that this is the only real root of the sextic above \(3\), hence its largest real root. This establishes the target identification by elementary derivative/sign reasoning in addition to the independently executed Sturm arithmetic. No claim about the universal quantum supremum follows from either root argument.

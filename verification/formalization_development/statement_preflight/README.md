# Final assembly statement preflight

This is development integration work, not a final adversarial audit. The actual
`SOS.compact_identity`, `OperatorTheorem` and `Main` builds are deliberately not
triggered by this preflight while their finite certificates are still closing.

## Scope inspected

The inspected production modules are `OperatorTheorem`, `Main`, `LowerValue`,
`Strategy`, `StrategyTransport`, `HilbertULift`, `Operator`, `OperatorUpper`,
`Tensor`, `POVMConstruction`, `POVMDilation`, `POVMTransfer`, `POVMProbabilities`,
`POVMTransport`, `Measurements`, `Events`, `OperatorRoot`, `SOSIdentity`,
`Attainment`, `AttainmentSpectralLink` and `AttainmentSourceHeader`.

The source inspection found no direct integration defect requiring a production
edit:

- `Strategy.{u,v}` has independent local universes. Its local fields require only
  complex inner-product normed groups and completeness. There is no
  finite-dimensional, countability, separability, basis or matrix-size premise.
- `State` is a positive complex-linear functional on the entire bounded-operator
  algebra, normalized on the identity. It has no normality, density-operator,
  trace-class, product-state or vector-state condition. The real-part expectation
  preserves the positive-functional order inequality.
- `POVM` has all five positive effects and their sum equal to the identity.
  Projectivity is introduced only after a proved dilation.
- `HTensor` explicitly completes the algebraic Hilbert tensor product. No
  completeness requirement is imposed on the algebraic tensor product itself.
- Both local settings dilate into the same local space with the same `commonJ`.
  The enlarged state is pulled back along the one fixed tensor inclusion.
  All joint probabilities are simultaneously preserved. Compression is not
  treated as a same-party algebra homomorphism.
- The commuting-PVM upper statement assumes only cross-party commutation;
  its unitary precursor imposes order five and unitarity but no same-party
  commutation. The final local POVM statement adds no restriction to `State`.
- The concrete attainer has both local spaces literally
  `EuclideanSpace ℂ (Fin 5)`, and the matrix coordinate space is
  `EuclideanSpace ℂ (Fin 5 × Fin 5)`. `physicalVector_eigen` is an equation in
  the whole completed physical tensor product. The public attainment module
  also imports the checked source-header-to-Schmidt-amplitudes theorem.
- `Strategy.lift` transports this same physical strategy via local unitary
  equivalences onto universe lifts. `quantumValues` contains exactly values of
  actual strategies; the lower proof does not insert an artificial real value.
- The proposed final `IsGreatest`, supremum and sextic-root assembly uses that
  lower membership and the unrestricted universal upper statement. Nonemptiness
  and boundedness for the conditionally complete real supremum are supplied by
  the actual attaining strategy and the upper inequality.

## Lightweight kernel probe

`ScopePreflight.lean` imports checked lower and conditional upper interfaces,
never `Main` or `SOSIdentity`. Its upper inequality is an explicit theorem
hypothesis. It checks independently quantified local universes, the exact local
five-dimensional type equalities, lifted physical attainment, and the proposed
final supremum/sextic conjunction assembly. It is not a replacement upper-bound
proof and introduces no axiom.

The build result is recorded in `scope_build.log`. Source inspection and this
conditional probe do not constitute a complete production theorem replay.

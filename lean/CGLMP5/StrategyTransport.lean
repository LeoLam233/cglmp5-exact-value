import CGLMP5.Strategy
import CGLMP5.POVMTransport
import CGLMP5.HilbertULift

noncomputable section
namespace CGLMP5
universe u v w z

/-- Every strategy is preserved exactly under a change to isometrically equivalent local Hilbert spaces. -/
def Strategy.transport (S : Strategy.{u,v})
    {H : Type w} {K : Type z} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : S.Alice ≃ₗᵢ[ℂ] H) (f : S.Bob ≃ₗᵢ[ℂ] K) : Strategy.{w,z} where
  Alice := H
  Bob := K
  state := transportState S.state e f
  aliceMeasurements x := (S.aliceMeasurements x).transport e
  bobMeasurements y := (S.bobMeasurements y).transport f

@[simp] theorem Strategy.transport_value (S : Strategy.{u,v})
    {H : Type w} {K : Type z} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : S.Alice ≃ₗᵢ[ℂ] H) (f : S.Bob ≃ₗᵢ[ℂ] K) :
    (S.transport e f).value = S.value := by
  exact cglmp_transport S.state S.aliceMeasurements S.bobMeasurements e f

/-- The concrete finite strategy can be included in every larger universe without altering its value. -/
def Strategy.lift (S : Strategy.{0,0}) : Strategy.{u,v} :=
  S.transport (H := ULift.{u} S.Alice) (K := ULift.{v} S.Bob)
    (LinearIsometryEquiv.ulift ℂ S.Alice).symm (LinearIsometryEquiv.ulift ℂ S.Bob).symm

@[simp] theorem Strategy.lift_value (S : Strategy.{0,0}) : (S.lift.{u,v}).value = S.value :=
  S.transport_value _ _

end CGLMP5

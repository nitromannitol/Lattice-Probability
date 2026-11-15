import LatticeProb.Prob.AEPrerequisiteStoppedHistory
import LatticeProb.Prob.StrictBallExit
import LatticeProb.Prob.BrownianOpenExitStopping

/-! # Stopped histories at concentric ball exits -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- An event in the raw history at the inner exit has an almost-surely equal
representative observable from the outer exit clock and stopped path. -/
theorem ball_exit_history_ae_representative
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hrR : r < R)
    (hstart : ∀ᵐ ω ∂μ, X 0 ω ∈ ball z r)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤)
    {A : Set Ω}
    (hA : MeasurableSet[(isStoppingTime_openExitTime hm hc
      (isOpen_ball : IsOpen (ball z r))).measurableSpace] A) :
    ∃ B : Set Ω, MeasurableSet[MeasurableSpace.comap
      (fun ω => (openExitTime X (ball z R) ω,
        stoppedPath (openExitTime X (ball z R) ω) (pathMap X hc ω))) inferInstance] B ∧
      ∀ᵐ ω ∂μ, ω ∈ A ↔ ω ∈ B := by
  apply stopped_history_ae_representative_of_lt hm hc
    (isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z r)))
    (openExitTime X (ball z R)) μ _ hA
  exact ae_openExitTime_ball_lt_of_lt μ X z hrR (Filter.Eventually.of_forall hc) hstart hfin

end LatticeProb

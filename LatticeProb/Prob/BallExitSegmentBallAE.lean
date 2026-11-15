import LatticeProb.Prob.NestedExitSegmentBallAE
import LatticeProb.Prob.BrownianOpenExitStopping
import LatticeProb.Prob.BallExitRadius

/-! # Segment events between almost surely finite ball exits -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- Ball containment between nested open-ball exits has a representative measurable at
    the later exit when that exit is almost surely finite. -/
theorem exists_measurableSet_ball_subset_nested_exit_segment_ae
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) {r R a : ℝ} (hr : r ≤ R) (ha : 0 < a)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤) :
    ∃ s : Set Ω,
      MeasurableSet[(isStoppingTime_openExitTime hm hc
        (isOpen_ball : IsOpen (ball z R))).measurableSpace] s ∧
      ∀ᵐ ω ∂μ, (ω ∈ s ↔ ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
        ((openExitTime X (ball z r) ω).toNNReal : ℝ)
        ((openExitTime X (ball z R) ω).toNNReal : ℝ)) := by
  exact exists_measurableSet_ball_subset_segment_ae hm hc
    (isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z r)))
    (isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z R)))
    (fun ω => monotone_openExitTime_ball X ω z hr) hfin ha

end LatticeProb

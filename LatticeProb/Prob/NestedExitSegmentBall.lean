import LatticeProb.Prob.BrownianOpenExitStopping
import LatticeProb.Prob.BallExitRadius
import LatticeProb.Prob.StoppedSegmentBall

/-! # Ball containment between nested exit times -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace LatticeProb

/-- For finite nested ball exits of a continuous process, containment of a positive-radius
ball in the intervening trace is measurable at the later exit time. -/
theorem measurableSet_ball_subset_nested_exit_segment
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) {r R a : ℝ} (hr : r ≤ R) (ha : 0 < a)
    (hfin : ∀ ω, openExitTime X (ball z R) ω ≠ ⊤) :
    MeasurableSet[(isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z R))).measurableSpace]
      {ω | ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
        ((openExitTime X (ball z r) ω).toNNReal : ℝ)
        ((openExitTime X (ball z R) ω).toNNReal : ℝ)} := by
  have hle : ∀ ω, openExitTime X (ball z r) ω ≤ openExitTime X (ball z R) ω :=
    fun ω => monotone_openExitTime_ball X ω z hr
  have hfin' : ∀ ω, openExitTime X (ball z r) ω ≠ ⊤ :=
    fun ω => ne_top_of_le_ne_top (hfin ω) (hle ω)
  have hσ : IsStoppingTime (natFiltration X hm)
      (fun ω => ((openExitTime X (ball z r) ω).toNNReal : ℝ≥0∞)) := by
    simpa only [ENNReal.coe_toNNReal (hfin' _)] using
      (isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z r)))
  have hτ : IsStoppingTime (natFiltration X hm)
      (fun ω => ((openExitTime X (ball z R) ω).toNNReal : ℝ≥0∞)) := by
    simpa only [ENNReal.coe_toNNReal (hfin _)] using
      (isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z R)))
  have hord : ∀ ω, (openExitTime X (ball z r) ω).toNNReal ≤
      (openExitTime X (ball z R) ω).toNNReal :=
    fun ω => (ENNReal.toNNReal_le_toNNReal (hfin' ω) (hfin ω)).2 (hle ω)
  have heq : (fun ω => ((openExitTime X (ball z R) ω).toNNReal : ℝ≥0∞)) =
      openExitTime X (ball z R) := funext fun ω => ENNReal.coe_toNNReal (hfin ω)
  have h := measurableSet_ball_subset_stopped_segment hm hc hσ hτ hord ha
  exact (IsStoppingTime.measurableSpace_mono hτ
    (isStoppingTime_openExitTime hm hc (isOpen_ball : IsOpen (ball z R)))
    (fun ω => le_of_eq (congrFun heq ω))) _ h

end LatticeProb

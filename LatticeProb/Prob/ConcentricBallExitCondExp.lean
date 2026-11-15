import LatticeProb.Prob.CompletedHistoryCondExp
import LatticeProb.Prob.ConcentricBallExitHistory
import LatticeProb.Prob.BrownianPathMap

/-! # Conditional bounds at concentric ball exits -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- The exit time from an open set is a stopping time for the completed
natural filtration. -/
theorem isStoppingTime_completed_openExitTime
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (μ : Measure Ω) {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) :
    IsStoppingTime (completedFiltration (natFiltration X hm) μ) (openExitTime X U) := by
  intro t
  exact le_eventuallyMeasurableSpace _ (isStoppingTime_openExitTime hm hc hU t)

/-- A lower bound conditioned on the outer exit clock and stopped path transfers to
an ambient-measurable subhistory of the completed inner exit history. -/
theorem concentric_ball_exit_condExp_const_le
    {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hrR : r < R)
    (hstart : ∀ᵐ ω ∂μ, X 0 ω ∈ ball z r)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤)
    {H : MeasurableSpace Ω} (hH : H ≤ m)
    (hHS : H ≤ (@isStoppingTime_completed_openExitTime Ω m d X hm hc μ _
      (isOpen_ball : IsOpen (ball z r))).measurableSpace)
    {f : Ω → ℝ} (hf : Integrable f μ) {p : ℝ}
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[f | MeasurableSpace.comap
      (fun ω => (openExitTime X (ball z R) ω,
        stoppedPath (openExitTime X (ball z R) ω) (pathMap X hc ω))) inferInstance] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[f | H] ω := by
  let : MeasurableSpace Ω := m
  have hT : Measurable (openExitTime X (ball z R)) :=
    measurable_openExitTime hm hc isOpen_ball
  have hpath : Measurable (pathMap X hc) :=
    measurable_pathMap X (fun t => (hm t).measurable) hc
  have hG : MeasurableSpace.comap
      (fun ω => (openExitTime X (ball z R) ω,
        stoppedPath (openExitTime X (ball z R) ω) (pathMap X hc ω))) inferInstance ≤ m := by
    exact (hT.prodMk (continuous_stoppedPath.measurable.comp (hT.prodMk hpath))).comap_le
  apply completed_stopped_history_condExp_const_le_of_lt hm hc
    (openExitTime X (ball z r)) (openExitTime X (ball z R)) μ
    (isStoppingTime_completed_openExitTime hm hc μ isOpen_ball) _ hH hHS hG hf hp
  exact ae_openExitTime_ball_lt_of_lt μ X z hrR (Filter.Eventually.of_forall hc) hstart hfin

end LatticeProb

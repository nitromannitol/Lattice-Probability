import LatticeProb.Prob.ConcentricBallExitCondExp
import LatticeProb.Prob.BallExitHistory

/-! # Conditional bounds for stopped ball-exit histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A raw stopping history is contained in the corresponding history of the
filtration completed using the ambient measure. -/
theorem stopped_history_le_completed
    {Ω : Type*} [m : MeasurableSpace Ω] (F : Filtration ℝ≥0 m)
    (μ : Measure Ω) (S : Ω → ℝ≥0∞)
    (hS : IsStoppingTime F S)
    (hSc : IsStoppingTime (completedFiltration F μ) S) :
    hS.measurableSpace ≤ hSc.measurableSpace := by
  intro A hA
  have hraw := (hS.measurableSet A).mp hA
  apply (hSc.measurableSet A).mpr
  constructor
  · have hle : ∀ t, F t ≤ (completedFiltration F μ) t :=
      fun _ => le_eventuallyMeasurableSpace
    exact (iSup_le fun t => (hle t).trans
      (le_iSup (fun t => (completedFiltration F μ) t) t)) A hraw.1
  · intro t
    exact le_eventuallyMeasurableSpace _ (hraw.2 t)

/-- A conditional lower bound given an outer exit observation also holds given
the raw natural history at the strictly smaller inner exit. -/
theorem ballExitHistory_condExp_const_le_of_outer_observation
    {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (z : EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (hr : Monotone r)
    (k : ℕ) {R : ℝ} (hrR : r k < R)
    (hstart : ∀ᵐ ω ∂μ, X 0 ω ∈ ball z (r k))
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤)
    {f : Ω → ℝ} (hf : Integrable f μ) {p : ℝ}
    (hp : ∀ᵐ ω ∂μ, p ≤ μ[f | MeasurableSpace.comap
      (fun ω => (openExitTime X (ball z R) ω,
        stoppedPath (openExitTime X (ball z R) ω) (pathMap X hc ω))) inferInstance] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[f | ballExitHistory X hm hc z r hr k] ω := by
  apply concentric_ball_exit_condExp_const_le hm hc μ z hrR hstart hfin
    ((ballExitHistory X hm hc z r hr).le k) ?_ hf hp
  exact stopped_history_le_completed (natFiltration X hm) μ _
    (isStoppingTime_openExitTime hm hc isOpen_ball)
    (isStoppingTime_completed_openExitTime hm hc μ isOpen_ball)

end LatticeProb

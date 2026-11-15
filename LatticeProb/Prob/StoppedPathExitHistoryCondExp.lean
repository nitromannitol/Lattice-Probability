import LatticeProb.Prob.BallExitHistoryCondExp
import LatticeProb.Prob.OpenExitStoppedPath

/-! # Conditional bounds from stopped paths at ball exits -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace LatticeProb

/-- A conditional lower bound given a later stopped path also holds given the
raw natural history at a strictly smaller concentric ball exit. -/
theorem ballExitHistory_condExp_const_le_of_outer_stoppedPath
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
      (fun ω => stoppedPath (openExitTime X (ball z R) ω) (pathMap X hc ω))
      inferInstance] ω) :
    ∀ᵐ ω ∂μ, p ≤ μ[f | ballExitHistory X hm hc z r hr k] ω := by
  let P := fun ω => stoppedPath (openExitTime X (ball z R) ω) (pathMap X hc ω)
  let Q := fun ω => (openExitTime X (ball z R) ω, P ω)
  have hQP : MeasurableSpace.comap Q inferInstance ≤ MeasurableSpace.comap P inferInstance := by
    exact ((measurable_openExitTime_stoppedPath hc isOpen_ball).prodMk
      (comap_measurable P)).comap_le
  have hPQ : MeasurableSpace.comap P inferInstance ≤ MeasurableSpace.comap Q inferInstance := by
    exact (measurable_snd.comp (comap_measurable Q)).comap_le
  have heq : MeasurableSpace.comap Q inferInstance = MeasurableSpace.comap P inferInstance :=
    le_antisymm hQP hPQ
  apply ballExitHistory_condExp_const_le_of_outer_observation hm hc μ z r hr k hrR hstart hfin hf
  change ∀ᵐ ω ∂μ, p ≤ μ[f | MeasurableSpace.comap Q inferInstance] ω
  rw [heq]
  exact hp

end LatticeProb

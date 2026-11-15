import LatticeProb.Prob.PathIntervalOscillationMeasurable

/-! # Measurable oscillation between ball exits -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LatticeProb.UnboundedRayIntervalIntegrand

/-- For a fixed radius, the exit clock is measurable as a function of the path. -/
theorem measurable_ballClock_fixed_radius {d : ℕ} (r : ℝ) :
    Measurable (fun f : Path d => ballClock f r) := by
  apply measurable_of_Iic
  intro a
  by_cases ha : a = ⊤
  · subst a
    simp only [Set.preimage, Set.mem_Iic, le_top, ofPred_true]
    exact MeasurableSet.univ
  · rw [← ENNReal.coe_toNNReal ha]
    have hc : Continuous (fun f : Path d => (f, r)) :=
      continuous_id.prodMk continuous_const
    exact ((isClosed_ballClock_le a.toNNReal).preimage hc).measurableSet

/-- A finite ball exit is a measurable event. -/
theorem measurableSet_ballClock_ne_top {d : ℕ} (r : ℝ) :
    MeasurableSet {f : Path d | ballClock f r ≠ ⊤} := by
  exact ((measurableSet_singleton ⊤).preimage (measurable_ballClock_fixed_radius r)).compl

/-- Oscillation between totalized ball exits is measurable. Infinite exit times
are sent to zero by `ENNReal.toNNReal`. -/
theorem measurableSet_ballClock_oscillation_le {d : ℕ} (r₁ r₂ η : ℝ) :
    MeasurableSet {f : Path d | ∀ s ∈ Icc (ballClock f r₁).toNNReal
        (ballClock f r₂).toNNReal,
      ∀ t ∈ Icc (ballClock f r₁).toNNReal (ballClock f r₂).toNNReal,
        dist (f s) (f t) ≤ η} := by
  have h₁ : Measurable (fun f : Path d => (ballClock f r₁).toNNReal) :=
    ENNReal.measurable_toNNReal.comp (measurable_ballClock_fixed_radius r₁)
  have h₂ : Measurable (fun f : Path d => (ballClock f r₂).toNNReal) :=
    ENNReal.measurable_toNNReal.comp (measurable_ballClock_fixed_radius r₂)
  exact measurableSet_interval_oscillation_le id _ _ η measurable_id h₁ h₂

end LatticeProb.UnboundedRayIntervalIntegrand

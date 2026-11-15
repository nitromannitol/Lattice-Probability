import LatticeProb.Prob.CellConfigIntervalDistance

/-! # Cell configuration distance for stable restrictions -/

set_option autoImplicit false

open Set

namespace ReflectedGMS.GMS

/-- Admissibility depends on the radius only through the two cell restrictions. -/
theorem admissibleAt_iff_of_restrict_eq (H H' : CellConfig) (r s : ℝ)
    (hH : H.restrict (Metric.ball 0 r) = H.restrict (Metric.ball 0 s))
    (hH' : H'.restrict (Metric.ball 0 r) = H'.restrict (Metric.ball 0 s))
    (f : Plane ≃ₜ Plane) :
    CellConfig.AdmissibleAt H H' r f ↔ CellConfig.AdmissibleAt H H' s f := by
  unfold CellConfig.AdmissibleAt
  rw [hH, hH']

/-- Stable restrictions and the absence of an admissible map at one reference radius
provide a lower bound for the configuration distance. -/
theorem ofReal_interval_mul_exp_le_dCC_of_stable_restrict
    (H H' : CellConfig) {a b s : ℝ} (ha : 0 ≤ a)
    (hH : ∀ r ∈ Ioo a b, H.restrict (Metric.ball 0 r) = H.restrict (Metric.ball 0 s))
    (hH' : ∀ r ∈ Ioo a b, H'.restrict (Metric.ball 0 r) = H'.restrict (Metric.ball 0 s))
    (h : ∀ f : Plane ≃ₜ Plane, ¬ CellConfig.AdmissibleAt H H' s f) :
    ENNReal.ofReal ((b - a) * Real.exp (-b)) ≤ CellConfig.dCC H H' := by
  apply ofReal_interval_mul_exp_le_dCC_of_no_admissible H H' ha
  intro r hr f hf
  exact h f ((admissibleAt_iff_of_restrict_eq H H' r s (hH r hr) (hH' r hr) f).mp hf)

end ReflectedGMS.GMS

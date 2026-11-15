import LatticeProb.Bonanno.ReflectedGMS.GeomTop.GMSTopologyBounds

/-! # A lower bound for cell configuration distance -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GMS

/-- An interval on which no homeomorphism is admissible gives a lower bound
for the configuration distance. -/
theorem ofReal_interval_mul_exp_le_dCC_of_no_admissible
    (H H' : CellConfig) {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ r ∈ Ioo a b, ∀ f : Plane ≃ₜ Plane, ¬ CellConfig.AdmissibleAt H H' r f) :
    ENNReal.ofReal ((b - a) * Real.exp (-b)) ≤ CellConfig.dCC H H' := by
  by_cases hab : a < b
  · have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun _ hr => lt_of_le_of_lt ha hr.1
    have hconst : ENNReal.ofReal ((b - a) * Real.exp (-b)) =
        ∫⁻ _ in Ioo a b, ENNReal.ofReal (Real.exp (-b)) := by
      rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
    rw [hconst]
    unfold CellConfig.dCC
    calc
      _ ≤ ∫⁻ r in Ioo a b,
          min (ENNReal.ofReal (Real.exp (-r)))
            (⨅ (f : Plane ≃ₜ Plane) (_ : CellConfig.AdmissibleAt H H' r f),
              CellConfig.distortion H H' r f) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro r hr
        have hi : (⨅ (f : Plane ≃ₜ Plane) (_ : CellConfig.AdmissibleAt H H' r f),
            CellConfig.distortion H H' r f) = ⊤ := by
          apply iInf_eq_top.mpr
          intro f
          exact iInf_eq_top.mpr fun hf => (h r hr f hf).elim
        rw [hi, min_eq_left le_top]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hr.2.le))
      _ ≤ _ := lintegral_mono_set hsub
  · have hba : b - a ≤ 0 := sub_nonpos.mpr (le_of_not_gt hab)
    rw [ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg hba (Real.exp_pos _).le)]
    exact zero_le

end ReflectedGMS.GMS

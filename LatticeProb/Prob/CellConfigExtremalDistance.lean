import LatticeProb.Bonanno.ReflectedGMS.GeomTop.GMSTopologyBounds

/-! # Extremal distance between cell configurations -/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.GMS

/-- If no plane homeomorphism is admissible at any positive radius, the
configuration distance attains its upper bound. -/
theorem dCC_eq_one_of_no_admissible (H H' : CellConfig)
    (h : ∀ r : ℝ, 0 < r → ∀ f : Plane ≃ₜ Plane, ¬ CellConfig.AdmissibleAt H H' r f) :
    CellConfig.dCC H H' = 1 := by
  unfold CellConfig.dCC
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-r)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hi : (⨅ (f : Plane ≃ₜ Plane) (_ : CellConfig.AdmissibleAt H H' r f),
          CellConfig.distortion H H' r f) = ⊤ := by
        apply iInf_eq_top.mpr
        intro f
        exact iInf_eq_top.mpr fun hf => (h r hr f hf).elim
      rw [hi]
      exact min_eq_left le_top
    _ = 1 := by
      rw [GeomTop.GMSTopology.lintegral_exp_neg_Ioi, neg_zero, Real.exp_zero, ENNReal.ofReal_one]

end ReflectedGMS.GMS

import LatticeProb.Prob.CellConfigWalkMeasurable

/-! # Moments for cell configurations with conductances bounded below by one -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigWalk

/-- Reciprocal conductance is bounded by conductance when every nonzero
conductance is at least one. -/
theorem piStar_le_pi_of_one_le (H : GMSSpace) (K : Cell)
    (hc : ∀ K' : H.1.cells, H.1.c K K' = 0 ∨ 1 ≤ H.1.c K K') :
    H.1.piStar K ≤ H.1.pi K := by
  have hle : ∀ K' : H.1.cells, (H.1.c K K')⁻¹ ≤ H.1.c K K' := by
    intro K'
    rcases hc K' with hz | h1
    · simp only [hz, inv_zero, le_refl]
    · exact (inv_le_one_of_one_le₀ h1).trans h1
  have hs := summable_c H.2 K
  have hsi : Summable fun K' : H.1.cells => (H.1.c K K')⁻¹ :=
    Summable.of_nonneg_of_le (fun K' => inv_nonneg.mpr (H.2.c_nonneg K K')) hle hs
  exact hsi.tsum_le_tsum hle hs

/-- For conductances that are zero or at least one, the ordinary rooted
conductance moment also bounds the reciprocal-conductance moment. -/
theorem finiteExpectation_of_one_le_conductance (μ : Measure GMSSpace)
    (H₀ : GMSSpace → Cell)
    (hroot : ∀ H, H₀ H ∈ H.1.cells ∧ (0 : Plane) ∈ (H₀ H : Set Plane))
    (hc : ∀ᵐ H ∂μ, ∀ K' : H.1.cells,
      H.1.c (H₀ H) K' = 0 ∨ 1 ≤ H.1.c (H₀ H) K')
    (hfin : ∫⁻ H, ENNReal.ofReal (Metric.diam (H₀ H : Set Plane) ^ 2 /
      CellConfig.area (H₀ H) * H.1.pi (H₀ H)) ∂μ < ∞) :
    FiniteExpectation μ := by
  refine ⟨H₀, hroot, hfin, ?_⟩
  refine (lintegral_mono_ae ?_).trans_lt hfin
  filter_upwards [hc] with H hH
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (piStar_le_pi_of_one_le H (H₀ H) hH)
    (div_nonneg (sq_nonneg _) (ENNReal.toReal_nonneg))

end LatticeProb.CellConfigWalk

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.FieldBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.PieceCost




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

 
def gradientBox : Set ℂ := Icc (-2:ℝ) 3 ×ℂ Icc (-2:ℝ) 3

theorem convex_gradientBox : Convex ℝ gradientBox :=
  ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

theorem closedSquareAnnulus_subset_gradientBox {z : ℂ}
    (hz : z ∈ Exponent.PolygonalCost.closedSquareAnnulus) : z ∈ gradientBox := by
  simp only [Exponent.PolygonalCost.closedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm,
    mem_Icc, mem_Ioo] at hz
  simp only [gradientBox, Complex.mem_reProdIm, mem_Icc]
  exact ⟨⟨by linarith [hz.1.1.1], by linarith [hz.1.1.2]⟩,
    ⟨by linarith [hz.1.2.1], by linarith [hz.1.2.2]⟩⟩

theorem inwardMap_mem_gradientBox (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256)
    {z : ℂ} (hz : z ∈ Exponent.PolygonalCost.closedSquareAnnulus) :
    inwardMap a z ∈ gradientBox := by
  have h := inwardMap_closed_to_cleared a ha0 ha hz
  simp only [clearedSquareAnnulus, mem_sdiff, Complex.mem_reProdIm,
    mem_Icc, mem_Ioo] at h
  simp only [gradientBox, Complex.mem_reProdIm, mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [h.1.1.1, h.1.1.2,
    h.1.2.1, h.1.2.2]

 
theorem inwardMap_field_difference_le (a G : ℝ) (ha0 : 0 ≤ a)
    (ha : a ≤ 1/256) (hG0 : 0 ≤ G) (f : ℂ → ℝ)
    (hfd : ∀ z ∈ gradientBox, DifferentiableAt ℝ f z)
    (hG : ∀ z ∈ gradientBox, ‖fderiv ℝ f z‖ ≤ G)
    {z : ℂ} (hz : z ∈ Exponent.PolygonalCost.closedSquareAnnulus) :
    f (inwardMap a z) ≤ f z + 32 * Real.sqrt 2 * a * G := by
  have hdiff : ‖f (inwardMap a z) - f z‖ ≤
      G * ‖inwardMap a z-z‖ :=
    convex_gradientBox.norm_image_sub_le_of_norm_fderiv_le
      hfd hG (closedSquareAnnulus_subset_gradientBox hz)
      (inwardMap_mem_gradientBox a ha0 ha hz)
  have hdis := inwardMap_displacement a ha0 z
  have hmul : G*‖inwardMap a z-z‖ ≤ G*(32*Real.sqrt 2*a) :=
    mul_le_mul_of_nonneg_left hdis hG0
  have hbound := hdiff.trans hmul
  rw [Real.norm_eq_abs] at hbound
  nlinarith [le_abs_self (f (inwardMap a z)-f z)]


end SupercriticalLQGUniqueness.Exponent.InwardMap

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.Separation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.ComplexMap




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

private theorem inwardAxis_preimage_unit (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256)
    {t : ℝ} (ht : inwardAxis a t ∈ Icc (0:ℝ) 1) :
    t ∈ Icc (0:ℝ) 1 := by
  have hm := inwardAxis_strictMono a ha0 ha
  constructor
  · by_contra h
    have hlt : t < 0 := lt_of_not_ge h
    have hf := hm hlt
    rw [inwardAxis_zero] at hf
    have := ht.1
    linarith
  · by_contra h
    have hlt : 1 < t := lt_of_not_ge h
    have hf := hm hlt
    rw [inwardAxis_one] at hf
    have := ht.2
    linarith

private theorem inwardAxis_maps_outerOpen (a : ℝ) (ha0 : 0 < a) (ha : a ≤ 1/256)
    {t : ℝ} (ht : t ∈ Ioo (-1:ℝ) 2) :
    inwardAxis a t ∈ Ioo (-1:ℝ) 2 := by
  have hm := inwardAxis_strictMono a ha0.le ha
  constructor
  · have h := hm ht.1
    rw [inwardAxis_neg_one] at h
    linarith
  · have h := hm ht.2
    rw [inwardAxis_two] at h
    linarith

theorem inwardMap_preimage_innerSquare (a : ℝ) (ha0 : 0 ≤ a)
    (ha : a ≤ 1/256) {z : ℂ}
    (hz : inwardMap a z ∈ Exponent.PaidDuality.innerSquare) : z ∈ Exponent.PaidDuality.innerSquare := by
  simp only [Exponent.PaidDuality.innerSquare, Complex.mem_reProdIm, mem_Icc,
    inwardMap_re, inwardMap_im] at hz ⊢
  exact ⟨inwardAxis_preimage_unit a ha0 ha hz.1,
    inwardAxis_preimage_unit a ha0 ha hz.2⟩

theorem inwardMap_maps_outerOpenSquare (a : ℝ) (ha0 : 0 < a)
    (ha : a ≤ 1/256) {z : ℂ}
    (hz : z ∈ Exponent.PaidDuality.outerOpenSquare) : inwardMap a z ∈ Exponent.PaidDuality.outerOpenSquare := by
  simp only [Exponent.PaidDuality.outerOpenSquare, Complex.mem_reProdIm, mem_Ioo,
    inwardMap_re, inwardMap_im] at hz ⊢
  exact ⟨inwardAxis_maps_outerOpen a ha0 ha hz.1,
    inwardAxis_maps_outerOpen a ha0 ha hz.2⟩

theorem inwardMap_preserves_disconnects (a : ℝ) (ha0 : 0 < a)
    (ha : a ≤ 1/256) (K : Set ℂ)
    (hK : LQGMetric.Disconnects K Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ) :
    LQGMetric.Disconnects (inwardMap a '' K)
      Exponent.PaidDuality.innerSquare Exponent.PaidDuality.outerOpenSquareᶜ := by
  let H : ℂ ≃ₜ ℂ := IsHomeomorph.homeomorph (inwardMap a)
    (inwardMap_isHomeomorph a ha0.le ha)
  intro x y γ hx hy
  have hx' : H.symm x ∈ Exponent.PaidDuality.innerSquare := by
    apply inwardMap_preimage_innerSquare a ha0.le ha
    change H (H.symm x) ∈ Exponent.PaidDuality.innerSquare
    simpa only [H.apply_symm_apply] using hx
  have hy' : H.symm y ∈ Exponent.PaidDuality.outerOpenSquareᶜ := by
    intro hyopen
    have hmap := inwardMap_maps_outerOpenSquare a ha0 ha hyopen
    have : y ∈ Exponent.PaidDuality.outerOpenSquare := by
      change H (H.symm y) ∈ Exponent.PaidDuality.outerOpenSquare at hmap
      simpa only [H.apply_symm_apply] using hmap
    exact hy this
  let γ' : Path (H.symm x) (H.symm y) := γ.map H.symm.continuous
  obtain ⟨p, hpγ, hpK⟩ := hK _ _ γ' hx' hy'
  rcases hpγ with ⟨t, rfl⟩
  refine ⟨H (γ' t), ?_, ?_⟩
  · refine ⟨t, ?_⟩
    change γ t = H (H.symm (γ t))
    exact (H.apply_symm_apply _).symm
  · exact ⟨γ' t, hpK, rfl⟩


end SupercriticalLQGUniqueness.Exponent.InwardMap

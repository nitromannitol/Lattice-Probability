import LatticeProb.Analysis.SphericalConeGeometry
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Polar coordinates on cones over the unit circle -/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace LatticeProb

/-- The radial cone over a set of unit directions selected by their arguments. -/
theorem complex_argument_radialCone (A : Set ℝ) :
    Ioo (0 : ℝ) 1 • {z : ℂ | ‖z‖ = 1 ∧ Complex.arg z ∈ A} =
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1 ∧ Complex.arg z ∈ A} := by
  rw [radialCone_unitSphere _ (fun _ h => h.1)]
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hl, hn, ha⟩
    refine ⟨hp, hl, ?_⟩
    simpa only [Complex.real_smul, Complex.arg_real_mul _ (inv_pos.mpr hp)] using ha
  · rintro ⟨hp, hl, ha⟩
    refine ⟨hp, hl, ?_, ?_⟩
    · rw [norm_smul_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel₀ (ne_of_gt hp)]
    · simpa only [Complex.real_smul, Complex.arg_real_mul _ (inv_pos.mpr hp)] using ha

/-- On the polar chart, an argument cone is a product of radial and angular sets. -/
theorem polarCoord_preimage_argument_radialCone (A : Set ℝ) :
    Complex.polarCoord.target ∩
      Complex.polarCoord.symm ⁻¹' (Ioo (0 : ℝ) 1 •
        {z : ℂ | ‖z‖ = 1 ∧ Complex.arg z ∈ A}) =
      Ioo (0 : ℝ) 1 ×ˢ (A ∩ Ioo (-Real.pi) Real.pi) := by
  rw [complex_argument_radialCone]
  ext p
  have hp : p ∈ Complex.polarCoord.target →
      ‖Complex.polarCoord.symm p‖ = p.1 ∧ Complex.arg (Complex.polarCoord.symm p) = p.2 := by
    intro h
    have h' := Complex.polarCoord.right_inv h
    rw [Complex.polarCoord_apply] at h'
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  constructor
  · rintro ⟨ht, hc⟩
    have h := hp ht
    rw [Complex.polarCoord_target] at ht
    simp only [mem_prod, mem_Ioi, mem_Ioo, mem_inter_iff] at ht ⊢
    change 0 < ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ < 1 ∧
      Complex.arg (Complex.polarCoord.symm p) ∈ A at hc
    rw [h.1, h.2] at hc
    exact ⟨⟨ht.1, hc.2.1⟩, hc.2.2, ht.2⟩
  · intro h
    simp only [mem_prod, mem_Ioo, mem_inter_iff] at h
    have ht : p ∈ Complex.polarCoord.target := by
      rw [Complex.polarCoord_target]
      exact ⟨h.1.1, h.2.2⟩
    have hh := hp ht
    refine ⟨ht, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, hh.1, hh.2]
    exact ⟨h.1.1, h.1.2, h.2.1⟩

end LatticeProb

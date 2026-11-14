import Mathlib

/-!
# Choosing a reciprocal mesh

Every sufficiently small positive real mesh becomes a reciprocal integer mesh after a time
scaling by a factor between one and two. The integer tends to infinity as the mesh tends to zero.
-/

set_option autoImplicit false

namespace LatticeProb

/-- The scaling factor needed to turn a positive mesh into a reciprocal integer mesh. -/
theorem reciprocal_mesh_scale_bounds {ε : ℝ} (hε : 0 < ε) :
    1 ≤ (⌈ε⁻¹⌉₊ : ℝ) * ε ∧ (⌈ε⁻¹⌉₊ : ℝ) * ε < 1 + ε := by
  have hlow := Nat.le_ceil ε⁻¹
  have hupp := Nat.ceil_lt_add_one (inv_nonneg.mpr hε.le)
  constructor
  · have h := mul_le_mul_of_nonneg_right hlow hε.le
    simpa [inv_mul_cancel₀ hε.ne'] using h
  · have h := mul_lt_mul_of_pos_right hupp hε
    simpa [add_mul, inv_mul_cancel₀ hε.ne'] using h

/-- A mesh smaller than one is rescaled by a factor in `[1, 2)`. -/
theorem reciprocal_mesh_scale_mem {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (⌈ε⁻¹⌉₊ : ℝ) * ε ∈ Set.Ico 1 2 := by
  obtain ⟨hlow, hupp⟩ := reciprocal_mesh_scale_bounds hε
  exact ⟨hlow, lt_trans hupp (by linarith)⟩

/-- The chosen integer is positive and gives exactly the reciprocal rescaled mesh. -/
theorem reciprocal_mesh_eq {ε : ℝ} (hε : 0 < ε) :
    0 < ⌈ε⁻¹⌉₊ ∧ ε / ((⌈ε⁻¹⌉₊ : ℝ) * ε) = (⌈ε⁻¹⌉₊ : ℝ)⁻¹ := by
  have hpos : ((0 : ℕ) : ℝ) < ε⁻¹ := by simpa using inv_pos.mpr hε
  have hn : 0 < ⌈ε⁻¹⌉₊ := Nat.lt_ceil.mpr hpos
  have hnr : (⌈ε⁻¹⌉₊ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  refine ⟨hn, ?_⟩
  field_simp

/-- The reciprocal mesh index eventually exceeds any prescribed integer. -/
theorem lt_reciprocal_mesh_index {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hsmall : ε < ((N : ℝ) + 1)⁻¹) : N < ⌈ε⁻¹⌉₊ := by
  apply Nat.lt_ceil.mpr
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have h := (lt_inv_comm₀ hε hden).mp hsmall
  linarith

end LatticeProb

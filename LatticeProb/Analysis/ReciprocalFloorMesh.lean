import Mathlib

/-! # Reciprocal mesh selection by rounding down -/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace LatticeProb

/-- Rounding down the reciprocal yields a scale between `1 - b` and `1`. -/
theorem reciprocal_floor_mesh_scale_bounds {b : ℝ} (hb : 0 < b) :
    1 - b < (⌊b⁻¹⌋₊ : ℝ) * b ∧ (⌊b⁻¹⌋₊ : ℝ) * b ≤ 1 := by
  have hl := Nat.lt_floor_add_one b⁻¹
  have hu := Nat.floor_le (inv_nonneg.mpr hb.le)
  have hl' := mul_lt_mul_of_pos_right hl hb
  have hu' := mul_le_mul_of_nonneg_right hu hb.le
  rw [inv_mul_cancel₀ hb.ne', add_mul, one_mul] at hl'
  rw [inv_mul_cancel₀ hb.ne'] at hu'
  exact ⟨by linarith, hu'⟩

/-- A mesh below one half produces a scaling factor in `(1/2, 1]`. -/
theorem reciprocal_floor_mesh_scale_mem {b : ℝ} (hb : 0 < b) (hbhalf : b < 1 / 2) :
    (⌊b⁻¹⌋₊ : ℝ) * b ∈ Ioc (1 / 2) 1 := by
  obtain ⟨hl, hu⟩ := reciprocal_floor_mesh_scale_bounds hb
  exact ⟨by linarith, hu⟩

/-- The floor index is positive and the scaled mesh is its reciprocal. -/
theorem reciprocal_floor_mesh_eq {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    0 < ⌊b⁻¹⌋₊ ∧ b / ((⌊b⁻¹⌋₊ : ℝ) * b) = (⌊b⁻¹⌋₊ : ℝ)⁻¹ := by
  have hinv : (1 : ℝ) ≤ b⁻¹ := (one_le_inv₀ hb).2 hb1.le
  have hn : 0 < ⌊b⁻¹⌋₊ := Nat.floor_pos.mpr hinv
  have hnr : (⌊b⁻¹⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  refine ⟨hn, ?_⟩
  field_simp

/-- The reciprocal floor index diverges as the positive mesh tends to zero. -/
theorem tendsto_reciprocal_floor_mesh_index :
    Tendsto (fun b : ℝ => ⌊b⁻¹⌋₊) (𝓝[>] 0) atTop :=
  tendsto_nat_floor_atTop.comp tendsto_inv_nhdsGT_zero

/-- The associated scaling factor tends to one. -/
theorem tendsto_reciprocal_floor_mesh_scale :
    Tendsto (fun b : ℝ => (⌊b⁻¹⌋₊ : ℝ) * b) (𝓝[>] 0) (𝓝 1) := by
  have hlo : Tendsto (fun b : ℝ => 1 - b) (𝓝[>] 0) (𝓝 1) := by
    have hid : Tendsto (fun b : ℝ => b) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left inf_le_left
    simpa using (tendsto_const_nhds.sub hid)
  have hhi : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact (reciprocal_floor_mesh_scale_bounds hb).1.le
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact (reciprocal_floor_mesh_scale_bounds hb).2

end LatticeProb

import LatticeProb.Prob.CellConfigExclusivePoint

/-! # Scaled exclusive anchors for cell configurations -/

set_option autoImplicit false

noncomputable section

open Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigContainingCell

/-- A point in a scaled cell can be moved to a point whose containing cell is uniquely
identified, at a distance bounded by the scaled cell diameter. -/
theorem exists_scaled_exclusive_anchor (H : GMSSpace) (K : H.1.cells)
    {ε : ℝ} (hε : 0 < ε) {z : Plane} (hz : ε⁻¹ • z ∈ (K.1 : Set Plane)) :
    ∃ w ∈ interior (K.1 : Set Plane),
      containingCell (H, w) = K.1 ∧
        dist (ε • w) z ≤ ε * Metric.diam (K.1 : Set Plane) := by
  obtain ⟨w, hw, honly⟩ := exists_interior_mem_only H K
  refine ⟨w, hw, containingCell_eq_of_mem_only H K w honly, ?_⟩
  have hd := Metric.dist_le_diam_of_mem K.1.isCompact.isBounded (interior_subset hw) hz
  have hm := mul_le_mul_of_nonneg_left hd hε.le
  calc
    dist (ε • w) z = dist (ε • w) (ε • (ε⁻¹ • z)) :=
      congrArg (dist (ε • w)) (smul_inv_smul₀ hε.ne' z).symm
    _ = ε * dist w (ε⁻¹ • z) := by rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hε]
    _ ≤ ε * Metric.diam (K.1 : Set Plane) := hm

end LatticeProb.CellConfigContainingCell

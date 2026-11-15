import LatticeProb.Prob.CellConfigScaledExclusivePoint

/-! # Uniform estimates for all containing cells -/

set_option autoImplicit false

noncomputable section

open Set Metric
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigContainingCell

/-- A uniform estimate for selected cells extends to all containing cells when
scaled cell diameters are small and the target varies little at that scale. -/
theorem all_containing_cell_dist_lt_of_selected {Y : Type*} [PseudoMetricSpace Y]
    (H : GMSSpace) (W : Cell → Y) (B : Plane → Y)
    {ε R η t : ℝ} (hε : 0 < ε) (hη : η ≤ 1)
    (hdiam : ∀ z ∈ closedBall (0 : Plane) R, ∀ K : H.1.cells,
      ε⁻¹ • z ∈ (K.1 : Set Plane) → ε * Metric.diam (K.1 : Set Plane) < η)
    (hselected : ∀ z ∈ closedBall (0 : Plane) (R + 1),
      dist (W (containingCell (H, ε⁻¹ • z))) (B z) < t)
    (hmod : ∀ u ∈ closedBall (0 : Plane) (R + 1),
      ∀ z ∈ closedBall (0 : Plane) (R + 1), dist u z < η → dist (B u) (B z) < t) :
    ∀ z ∈ closedBall (0 : Plane) R, ∀ K : H.1.cells,
      ε⁻¹ • z ∈ (K.1 : Set Plane) → dist (W K.1) (B z) < t + t := by
  intro z hz K hzK
  obtain ⟨w, _, hw, hdist⟩ := exists_scaled_exclusive_anchor H K hε hzK
  have hclose : dist (ε • w) z < η :=
    lt_of_le_of_lt hdist (hdiam z hz K hzK)
  have hwide : z ∈ closedBall (0 : Plane) (R + 1) :=
    closedBall_subset_closedBall (by linarith) hz
  have hanchor : ε • w ∈ closedBall (0 : Plane) (R + 1) := by
    apply mem_closedBall.mpr
    have hz' := mem_closedBall.mp hz
    have htri := dist_triangle (ε • w) z (0 : Plane)
    linarith
  have hselect := hselected (ε • w) hanchor
  rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul, hw] at hselect
  exact lt_of_le_of_lt (dist_triangle (W K.1) (B (ε • w)) (B z))
    (add_lt_add hselect (hmod (ε • w) hanchor z hwide hclose))

end LatticeProb.CellConfigContainingCell

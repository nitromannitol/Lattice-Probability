import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-!
# Interpolation across adjacent cells

A linearly interpolated walk is within the sum of the diameters of two adjacent
cells of either endpoint while it traverses their edge.
-/

set_option autoImplicit false

noncomputable section

open Set
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigInterpolation

variable (H : CellConfig)

/-- Representatives of adjacent cells are at distance at most the sum of the cell diameters. -/
theorem dist_representatives_le (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) {K L : H.cells} (hKL : H.Adj K L) :
    dist (p K) (p L) ≤ Metric.diam (K.1 : Set Plane) + Metric.diam (L.1 : Set Plane) := by
  obtain ⟨z, hzK, hzL⟩ := hH.adj_inter K L hKL
  exact (dist_triangle _ z _).trans (add_le_add
    (Metric.dist_le_diam_of_mem (K.1 : Cell).isCompact.isBounded (hp K) hzK)
    (Metric.dist_le_diam_of_mem (L.1 : Cell).isCompact.isBounded hzL (hp L)))

/-- During a holding interval the interpolated walk is within the two cell diameters of both
endpoint representatives. -/
theorem dist_interpolatedPath_endpoints_le (hH : H.IsCellConfiguration)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) {n : ℕ} {s : ℝ}
    (h1 : H.jumpTime ω n ≤ s) (h2 : s ≤ H.jumpTime ω (n + 1))
    (hadj : H.Adj (ω n) (ω (n + 1))) :
    dist (H.interpolatedPath p ω s) (p (ω n)) ≤
        Metric.diam ((ω n).1 : Set Plane) + Metric.diam ((ω (n + 1)).1 : Set Plane) ∧
    dist (H.interpolatedPath p ω s) (p (ω (n + 1))) ≤
        Metric.diam ((ω n).1 : Set Plane) + Metric.diam ((ω (n + 1)).1 : Set Plane) := by
  let u : ℝ := (s - H.jumpTime ω n) / (H.jumpTime ω (n + 1) - H.jumpTime ω n)
  have hd : 0 < H.jumpTime ω (n + 1) - H.jumpTime ω n := by
    rw [H.jumpTime_succ]
    simpa using hpos (ω n)
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr h1) hd.le
  have hu1 : u ≤ 1 := (div_le_one hd).2 (sub_le_sub_right h2 _)
  have hpdist := dist_representatives_le H hH p hp hadj
  rw [H.interpolatedPath_eq_lineMap hpos h1 h2]
  change dist (AffineMap.lineMap (p (ω n)) (p (ω (n + 1))) u) (p (ω n)) ≤ _ ∧
    dist (AffineMap.lineMap (p (ω n)) (p (ω (n + 1))) u) (p (ω (n + 1))) ≤ _
  rw [dist_lineMap_left, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hu0, abs_of_nonneg (sub_nonneg.mpr hu1)]
  constructor
  · exact (mul_le_of_le_one_left dist_nonneg hu1).trans hpdist
  · exact (mul_le_of_le_one_left dist_nonneg (by linarith)).trans hpdist

end LatticeProb.CellConfigInterpolation

end

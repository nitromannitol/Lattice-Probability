import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-!
# Stability of interpolated cell walks

Changing the representatives by a uniformly bounded amount changes the
interpolated walk by at most the scaled bound, for a fixed walk and clock.
-/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- At a nonnegative time, a fixed-clock interpolation preserves a uniform
bound on the distance between corresponding representatives. -/
theorem dist_interpolatedPath_le_of_dist_representatives_le (H : CellConfig)
    (p q : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {r s : ℝ} (hs : 0 ≤ s) (hclose : ∀ K, dist (p K) (q K) ≤ r) :
    dist (H.interpolatedPath p ω s) (H.interpolatedPath q ω s) ≤ r := by
  obtain ⟨n, hn, hn'⟩ := H.exists_mem_Ico hpos hunb hs
  let u : ℝ := (s - H.jumpTime ω n) / (H.jumpTime ω (n + 1) - H.jumpTime ω n)
  have hd : 0 < H.jumpTime ω (n + 1) - H.jumpTime ω n := by
    rw [H.jumpTime_succ]
    simpa using hpos (ω n)
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hn) hd.le
  have hu1 : u ≤ 1 := (div_le_one hd).2 (sub_le_sub_right hn'.le _)
  rw [H.interpolatedPath_eq_lineMap hpos hn hn'.le,
    H.interpolatedPath_eq_lineMap hpos hn hn'.le, dist_eq_norm]
  change ‖AffineMap.lineMap (p (ω n)) (p (ω (n + 1))) u -
    AffineMap.lineMap (q (ω n)) (q (ω (n + 1))) u‖ ≤ r
  rw [show AffineMap.lineMap (p (ω n)) (p (ω (n + 1))) u -
      AffineMap.lineMap (q (ω n)) (q (ω (n + 1))) u =
      AffineMap.lineMap (p (ω n) - q (ω n)) (p (ω (n + 1)) - q (ω (n + 1))) u by
    simpa only [vsub_eq_sub] using
      (AffineMap.lineMap_vsub_lineMap (V1 := Plane) (p (ω n)) (p (ω (n + 1)))
        (q (ω n)) (q (ω (n + 1))) u)]
  have hmem : AffineMap.lineMap (p (ω n) - q (ω n))
      (p (ω (n + 1)) - q (ω (n + 1))) u ∈ Metric.closedBall (0 : Plane) r := by
    apply (convex_closedBall (0 : Plane) r).segment_subset
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hclose (ω n))
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hclose (ω (n + 1)))
    exact lineMap_mem_segment ℝ (p (ω n) - q (ω n))
      (p (ω (n + 1)) - q (ω (n + 1))) ⟨hu0, hu1⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hmem

/-- Uniformly close representatives give uniformly close scaled walks, including
at scale zero. -/
theorem dist_interpolatedWalk_le_of_dist_representatives_le (H : CellConfig)
    (p q : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {r : ℝ} (hclose : ∀ K, dist (p K) (q K) ≤ r)
    (ε : ℝ≥0) (t : ℝ≥0) :
    dist ((H.interpolatedWalk p ε ω) t) ((H.interpolatedWalk q ε ω) t) ≤ (ε : ℝ) * r := by
  rw [show (H.interpolatedWalk p ε ω) t =
      (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) t,
    show (H.interpolatedWalk q ε ω) t =
      (ε : ℝ) • H.interpolatedPath q ω ((t : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) t]
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
    ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_left
    (dist_interpolatedPath_le_of_dist_representatives_le H p q ω hpos hunb
      (div_nonneg t.property (sq_nonneg (ε : ℝ))) hclose) ε.coe_nonneg

end LatticeProb.CellConfigInterpolation

end

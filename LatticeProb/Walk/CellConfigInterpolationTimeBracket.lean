import LatticeProb.Walk.CellConfigInterpolationDiameter

/-!
# Time intervals of interpolated walks

A finite observation time lies between consecutive rescaled jumps, and the
interpolated position is close to the representatives at both ends of the edge.
-/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- Any observation time is bracketed by consecutive scaled jumps. The path is
within the scaled sum of the two cell diameters of either endpoint. -/
theorem exists_scaled_jumpTime_bracket_dist_le (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) (t : ℝ≥0) :
    ∃ n : ℕ,
      (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (t : ℝ) ∧
      (t : ℝ) < (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) ∧
      dist ((H.interpolatedWalk p ε ω) t) ((ε : ℝ) • p (ω n)) ≤
        (ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)) ∧
      dist ((H.interpolatedWalk p ε ω) t) ((ε : ℝ) • p (ω (n + 1))) ≤
        (ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
          Metric.diam ((ω (n + 1)).1 : Set Plane)) := by
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  obtain ⟨n, hn, hn'⟩ := H.exists_mem_Ico hpos hunb
    (div_nonneg t.property (sq_nonneg (ε : ℝ)))
  have hb := dist_interpolatedPath_endpoints_le H hH p hp ω hpos hn hn'.le (hadj n)
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · rw [mul_comm]
    exact (le_div_iff₀ he).mp hn
  · exact (div_lt_iff₀ he).mp hn' |>.trans_eq (mul_comm _ _)
  · rw [show (H.interpolatedWalk p ε ω) t =
        (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) from
        congrFun (H.coe_interpolatedWalk hpos hunb ε) t]
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
      ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hb.1 ε.coe_nonneg
  · rw [show (H.interpolatedWalk p ε ω) t =
        (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) from
        congrFun (H.coe_interpolatedWalk hpos hunb ε) t]
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
      ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hb.2 ε.coe_nonneg

end LatticeProb.CellConfigInterpolation

end

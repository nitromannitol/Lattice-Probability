import LatticeProb.Walk.CellConfigInterpolationDiameter

/-! # Oscillation of interpolated cell walks along an edge -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- Two positions on the same linearly interpolated edge are at most the
endpoint distance apart. -/
theorem dist_interpolatedPath_le_edge (H : CellConfig)
    (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) {n : ℕ} {s t : ℝ}
    (hs₁ : H.jumpTime ω n ≤ s) (hs₂ : s ≤ H.jumpTime ω (n + 1))
    (ht₁ : H.jumpTime ω n ≤ t) (ht₂ : t ≤ H.jumpTime ω (n + 1)) :
    dist (H.interpolatedPath p ω s) (H.interpolatedPath p ω t) ≤
      dist (p (ω n)) (p (ω (n + 1))) := by
  let u : ℝ := (s - H.jumpTime ω n) / (H.jumpTime ω (n + 1) - H.jumpTime ω n)
  let v : ℝ := (t - H.jumpTime ω n) / (H.jumpTime ω (n + 1) - H.jumpTime ω n)
  have hd : 0 < H.jumpTime ω (n + 1) - H.jumpTime ω n := by
    rw [H.jumpTime_succ]
    simpa using hpos (ω n)
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hs₁) hd.le
  have hu1 : u ≤ 1 := (div_le_one hd).2 (sub_le_sub_right hs₂ _)
  have hv0 : 0 ≤ v := div_nonneg (sub_nonneg.mpr ht₁) hd.le
  have hv1 : v ≤ 1 := (div_le_one hd).2 (sub_le_sub_right ht₂ _)
  rw [H.interpolatedPath_eq_lineMap hpos hs₁ hs₂,
    H.interpolatedPath_eq_lineMap hpos ht₁ ht₂]
  change dist (AffineMap.lineMap (p (ω n)) (p (ω (n + 1))) u)
    (AffineMap.lineMap (p (ω n)) (p (ω (n + 1))) v) ≤ _
  rw [dist_lineMap_lineMap, Real.dist_eq]
  have huv : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact mul_le_of_le_one_left dist_nonneg huv

/-- Adjacent cells bound the oscillation of the interpolated edge by the sum
of their diameters. -/
theorem dist_interpolatedPath_le_cellDiameters (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) {n : ℕ} {s t : ℝ}
    (hs₁ : H.jumpTime ω n ≤ s) (hs₂ : s ≤ H.jumpTime ω (n + 1))
    (ht₁ : H.jumpTime ω n ≤ t) (ht₂ : t ≤ H.jumpTime ω (n + 1))
    (hadj : H.Adj (ω n) (ω (n + 1))) :
    dist (H.interpolatedPath p ω s) (H.interpolatedPath p ω t) ≤
      Metric.diam ((ω n).1 : Set Plane) + Metric.diam ((ω (n + 1)).1 : Set Plane) :=
  (dist_interpolatedPath_le_edge H p ω hpos hs₁ hs₂ ht₁ ht₂).trans
    (dist_representatives_le H hH p hp hadj)

/-- Stopping an interpolated walk at either of two times on one edge gives
paths uniformly close by the scaled distance between that edge's endpoints. -/
theorem dist_stopped_interpolatedWalk_le_edge (H : CellConfig)
    (p : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {ε : ℝ≥0} (hε : 0 < ε) (n : ℕ) (s u : ℝ≥0)
    (hs₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (s : ℝ))
    (hs₂ : (s : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (hu₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (u : ℝ))
    (hu₂ : (u : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (t : ℝ≥0) :
    dist ((H.interpolatedWalk p ε ω) (min t s))
      ((H.interpolatedWalk p ε ω) (min t u)) ≤
      (ε : ℝ) * dist (p (ω n)) (p (ω (n + 1))) := by
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  by_cases ht : (t : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω n
  · have hts : t ≤ s := by exact_mod_cast ht.trans hs₁
    have htu : t ≤ u := by exact_mod_cast ht.trans hu₁
    rw [min_eq_left hts, min_eq_left htu, dist_self]
    positivity
  · have ht' : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (t : ℝ) := (not_le.mp ht).le
    have h₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ ((min t s : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_min]; exact le_min ht' hs₁
    have h₂ : ((min t s : ℝ≥0) : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) := by
      simp only [NNReal.coe_min]; exact (min_le_right _ _).trans hs₂
    have h₃ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ ((min t u : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_min]; exact le_min ht' hu₁
    have h₄ : ((min t u : ℝ≥0) : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) := by
      simp only [NNReal.coe_min]; exact (min_le_right _ _).trans hu₂
    have h₁' : H.jumpTime ω n ≤ ((min t s : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2 :=
      (le_div_iff₀ he).2 (by simpa [mul_comm] using h₁)
    have h₂' : ((min t s : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2 ≤ H.jumpTime ω (n + 1) :=
      (div_le_iff₀ he).2 (by simpa [mul_comm] using h₂)
    have h₃' : H.jumpTime ω n ≤ ((min t u : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2 :=
      (le_div_iff₀ he).2 (by simpa [mul_comm] using h₃)
    have h₄' : ((min t u : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2 ≤ H.jumpTime ω (n + 1) :=
      (div_le_iff₀ he).2 (by simpa [mul_comm] using h₄)
    have hd := dist_interpolatedPath_le_edge H p ω hpos h₁' h₂' h₃' h₄'
    rw [show (H.interpolatedWalk p ε ω) (min t s) =
        (ε : ℝ) • H.interpolatedPath p ω (((min t s : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) (min t s),
      show (H.interpolatedWalk p ε ω) (min t u) =
        (ε : ℝ) • H.interpolatedPath p ω (((min t u : ℝ≥0) : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) (min t u)]
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
      ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hd ε.coe_nonneg

end LatticeProb.CellConfigInterpolation
end

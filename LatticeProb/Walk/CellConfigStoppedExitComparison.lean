import LatticeProb.Walk.CellConfigInterpolationDiameter
import LatticeProb.Walk.CellConfigExteriorExitClockGap

/-! # Stopping a cell walk within a single edge -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- If two stopping times lie in the same jump interval, the corresponding
stopped interpolations are uniformly close in terms of the adjacent cell
diameters. -/
theorem dist_stopped_interpolatedWalk_le_of_same_edge (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {ε : ℝ≥0} (hε : 0 < ε) (n : ℕ) (hadj : H.Adj (ω n) (ω (n + 1)))
    (s u : ℝ≥0)
    (hs₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (s : ℝ))
    (hs₂ : (s : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (hu₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (u : ℝ))
    (hu₂ : (u : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (t : ℝ≥0) :
    dist ((H.interpolatedWalk p ε ω) (min t s))
      ((H.interpolatedWalk p ε ω) (min t u)) ≤
      2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
        Metric.diam ((ω (n + 1)).1 : Set Plane))) := by
  let D : ℝ := Metric.diam ((ω n).1 : Set Plane) +
    Metric.diam ((ω (n + 1)).1 : Set Plane)
  have hD : 0 ≤ D := add_nonneg Metric.diam_nonneg Metric.diam_nonneg
  have he : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hε)
  have hedge : ∀ v : ℝ≥0,
      (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (v : ℝ) →
      (v : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) →
      dist ((H.interpolatedWalk p ε ω) v) ((ε : ℝ) • p (ω n)) ≤ (ε : ℝ) * D := by
    intro v hv₁ hv₂
    have hl : H.jumpTime ω n ≤ (v : ℝ) / (ε : ℝ) ^ 2 :=
      (le_div_iff₀ he).2 (by simpa [mul_comm] using hv₁)
    have hr : (v : ℝ) / (ε : ℝ) ^ 2 ≤ H.jumpTime ω (n + 1) :=
      (div_le_iff₀ he).2 (by simpa [mul_comm] using hv₂)
    have hd := (dist_interpolatedPath_endpoints_le H hH p hp ω hpos hl hr hadj).1
    rw [show (H.interpolatedWalk p ε ω) v =
        (ε : ℝ) • H.interpolatedPath p ω ((v : ℝ) / (ε : ℝ) ^ 2) from
      congrFun (H.coe_interpolatedWalk hpos hunb ε) v]
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg ε.coe_nonneg,
      ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hd ε.coe_nonneg
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
    have ha := hedge (min t s) h₁ h₂
    have hb := hedge (min t u) h₃ h₄
    have hc := dist_triangle ((H.interpolatedWalk p ε ω) (min t s))
      ((ε : ℝ) • p (ω n)) ((H.interpolatedWalk p ε ω) (min t u))
    rw [dist_comm ((ε : ℝ) • p (ω n))] at hc
    dsimp only [D] at ha hb ⊢
    linarith


/-- The interpolated walk stopped on exiting an open convex domain and the
same walk stopped at its first exterior representative differ only on the
final edge. -/
theorem stopped_interpolatedWalk_exit_comparison (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) {U : Set Plane} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hstart : (ε : ℝ) • p (ω 0) ∈ U)
    (hfin : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω ≠ ⊤) :
    ∃ n : ℕ,
      hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (n + 1 : ℕ) ∧
      let τ := continuousExitTime U 0 (H.interpolatedWalk p ε ω)
      τ ≠ ∞ ∧
      ∀ t : ℝ≥0,
        dist ((H.interpolatedWalk p ε ω) (min t τ.toNNReal))
          ((H.interpolatedWalk p ε ω) (min t
            ⟨(ε : ℝ) ^ 2 * H.jumpTime ω (n + 1),
              mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩)) ≤
          2 * ((ε : ℝ) * (Metric.diam ((ω n).1 : Set Plane) +
            Metric.diam ((ω (n + 1)).1 : Set Plane))) := by
  obtain ⟨n, hn, hf, hlo, hhi, _, _, _⟩ :=
    continuousExitTime_clock_gap_of_hitTime H hH p hp ω hpos hunb hadj hε hU hconv hstart hfin
  refine ⟨n, hn, hf, fun t => ?_⟩
  apply dist_stopped_interpolatedWalk_le_of_same_edge H hH p hp ω hpos hunb hε n (hadj n)
  · exact hlo.le
  · exact hhi
  · exact hlo.le.trans hhi
  · exact le_rfl


end LatticeProb.CellConfigInterpolation
end

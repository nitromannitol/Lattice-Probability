import LatticeProb.Walk.CellConfigInterpolationTimeBracket
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.HitTime
import Mathlib.Topology.MetricSpace.Thickening

/-! # A collar bound before the first exterior vertex -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigInterpolation

/-- Before a fixed jump, an interpolated cell walk remains close to a set
containing all earlier representatives. The edge leading out is included in
the diameter bound. -/
theorem interpolatedWalk_mem_cthickening_before_jump (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane) (N : ℕ) (d : ℝ)
    (hin : ∀ n < N, (ε : ℝ) • p (ω n) ∈ U)
    (hd : ∀ n < N, Metric.diam ((ω n).1 : Set Plane) +
      Metric.diam ((ω (n + 1)).1 : Set Plane) ≤ d)
    (t : ℝ≥0) (ht : (t : ℝ) < (ε : ℝ) ^ 2 * H.jumpTime ω N) :
    H.interpolatedWalk p ε ω t ∈ Metric.cthickening ((ε : ℝ) * d) U := by
  obtain ⟨n, hn, _, hdist, _⟩ :=
    exists_scaled_jumpTime_bracket_dist_le H hH p hp ω hpos hunb hadj hε t
  have hnN : n < N := by
    by_contra h
    have hm := (H.jumpTime_strictMono (ω := ω) hpos).monotone (Nat.le_of_not_gt h)
    have hm' := mul_le_mul_of_nonneg_left hm (sq_nonneg (ε : ℝ))
    linarith
  exact Metric.mem_cthickening_of_dist_le _ _ _ U (hin n hnN)
    (hdist.trans (mul_le_mul_of_nonneg_left (hd n hnN) ε.coe_nonneg))

/-- The same collar bound up to the first exterior representative. -/
theorem interpolatedWalk_mem_cthickening_before_exterior_hit (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (hadj : ∀ n, H.Adj (ω n) (ω (n + 1)))
    {ε : ℝ≥0} (hε : 0 < ε) (U : Set Plane) (N : ℕ) (d : ℝ)
    (hfirst : hitTime {K : H.cells | (ε : ℝ) • p K ∉ U} ω = (N : ℕ∞))
    (hd : ∀ n < N, Metric.diam ((ω n).1 : Set Plane) +
      Metric.diam ((ω (n + 1)).1 : Set Plane) ≤ d)
    (t : ℝ≥0) (ht : (t : ℝ) < (ε : ℝ) ^ 2 * H.jumpTime ω N) :
    H.interpolatedWalk p ε ω t ∈ Metric.cthickening ((ε : ℝ) * d) U := by
  apply interpolatedWalk_mem_cthickening_before_jump H hH p hp ω hpos hunb hadj hε U N d
    ?_ hd t ht
  intro n hn
  exact not_not.mp ((hitTime_eq_coe_iff.mp hfirst).2 n hn)

end LatticeProb.CellConfigInterpolation
end

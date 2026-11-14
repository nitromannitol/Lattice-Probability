import LatticeProb.Walk.CellConfigStoppedRepresentativeDistance

/-! # Stopped cell walks on adjacent clock edges -/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- If two stops lie on adjacent edges of the same holding-time clock,
nearby representatives give stopped paths whose distance is bounded by the
two scaled edge lengths and the scaled representative error. -/
theorem dist_stopped_interpolatedWalk_le_of_adjacent_edges
    (H : CellConfig) (p q : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {r : ℝ} (hclose : ∀ K, dist (p K) (q K) ≤ r)
    {ε : ℝ≥0} (hε : 0 < ε) (n : ℕ) (s u : ℝ≥0)
    (hs₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (s : ℝ))
    (hs₂ : (s : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (hu₁ : (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1) ≤ (u : ℝ))
    (hu₂ : (u : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω ((n + 1) + 1))
    (t : ℝ≥0) :
    dist ((H.interpolatedWalk p ε ω) (min t s))
      ((H.interpolatedWalk q ε ω) (min t u)) ≤
      (ε : ℝ) * dist (p (ω n)) (p (ω (n + 1))) +
        (ε : ℝ) * dist (p (ω (n + 1))) (p (ω ((n + 1) + 1))) +
        (ε : ℝ) * r := by
  let v : ℝ≥0 := ⟨(ε : ℝ) ^ 2 * H.jumpTime ω (n + 1),
    mul_nonneg (sq_nonneg _) (H.jumpTime_nonneg hpos (n + 1))⟩
  have hv₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (v : ℝ) := by
    exact mul_le_mul_of_nonneg_left
      ((H.jumpTime_strictMono (ω := ω) hpos).monotone (Nat.le_succ n)) (sq_nonneg _)
  have hv₂ : (v : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω ((n + 1) + 1) := by
    exact mul_le_mul_of_nonneg_left
      ((H.jumpTime_strictMono (ω := ω) hpos).monotone (Nat.le_succ (n + 1))) (sq_nonneg _)
  calc
    dist ((H.interpolatedWalk p ε ω) (min t s))
        ((H.interpolatedWalk q ε ω) (min t u)) ≤
      dist ((H.interpolatedWalk p ε ω) (min t s))
          ((H.interpolatedWalk p ε ω) (min t v)) +
        dist ((H.interpolatedWalk p ε ω) (min t v))
          ((H.interpolatedWalk q ε ω) (min t u)) := dist_triangle _ _ _
    _ ≤ (ε : ℝ) * dist (p (ω n)) (p (ω (n + 1))) +
        ((ε : ℝ) * dist (p (ω (n + 1))) (p (ω ((n + 1) + 1))) +
          (ε : ℝ) * r) := by
      apply add_le_add
      · exact dist_stopped_interpolatedWalk_le_edge H p ω hpos hunb hε n s v
          hs₁ hs₂ hv₁ (le_refl _) t
      · exact dist_stopped_interpolatedWalk_le_of_representatives_close H p q ω
          hpos hunb hclose hε (n + 1) v u (le_refl _) hv₂ hu₁ hu₂ t
    _ = _ := (add_assoc _ _ _).symm

end LatticeProb.CellConfigInterpolation
end

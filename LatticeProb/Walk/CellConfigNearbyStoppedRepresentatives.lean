import LatticeProb.Walk.CellConfigAdjacentStoppedRepresentatives

/-! # Stopped cell walks on nearby clock edges -/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- Two stops on the same or adjacent holding-clock edges give close stopped
paths when the representative error and all edge lengths are bounded. -/
theorem dist_stopped_interpolatedWalk_le_of_nearby_edges
    (H : CellConfig) (p q : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {r L : ℝ} (hclose : ∀ K, dist (p K) (q K) ≤ r)
    (hedge : ∀ i, dist (p (ω i)) (p (ω (i + 1))) ≤ L)
    {ε : ℝ≥0} (hε : 0 < ε) (n m : ℕ) (s u : ℝ≥0)
    (hs₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (s : ℝ))
    (hs₂ : (s : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (hu₁ : (ε : ℝ) ^ 2 * H.jumpTime ω m ≤ (u : ℝ))
    (hu₂ : (u : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (m + 1))
    (hnm : n ≤ m + 1) (hmn : m ≤ n + 1) (t : ℝ≥0) :
    dist ((H.interpolatedWalk p ε ω) (min t s))
      ((H.interpolatedWalk q ε ω) (min t u)) ≤
      2 * (ε : ℝ) * L + (ε : ℝ) * r := by
  have hL : 0 ≤ L := le_trans (dist_nonneg) (hedge 0)
  have he : 0 ≤ (ε : ℝ) := ε.coe_nonneg
  have hsame : ∀ K, dist (p K) (p K) ≤ (0 : ℝ) := by simp
  have hp : dist ((H.interpolatedWalk p ε ω) (min t s))
      ((H.interpolatedWalk p ε ω) (min t u)) ≤ 2 * (ε : ℝ) * L := by
    rcases lt_trichotomy n m with hlt | heq | hgt
    · have hm : m = n + 1 := by omega
      subst m
      have h := dist_stopped_interpolatedWalk_le_of_adjacent_edges H p p ω hpos hunb
        hsame hε n s u hs₁ hs₂ hu₁ hu₂ t
      have ha := mul_le_mul_of_nonneg_left (hedge n) he
      have hb := mul_le_mul_of_nonneg_left (hedge (n + 1)) he
      nlinarith
    · subst m
      have h := dist_stopped_interpolatedWalk_le_of_representatives_close H p p ω hpos hunb
        hsame hε n s u hs₁ hs₂ hu₁ hu₂ t
      have ha := mul_le_mul_of_nonneg_left (hedge n) he
      nlinarith
    · have hn : n = m + 1 := by omega
      subst n
      have h := dist_stopped_interpolatedWalk_le_of_adjacent_edges H p p ω hpos hunb
        hsame hε m u s hu₁ hu₂ hs₁ hs₂ t
      have ha := mul_le_mul_of_nonneg_left (hedge m) he
      have hb := mul_le_mul_of_nonneg_left (hedge (m + 1)) he
      rw [dist_comm] at h
      nlinarith
  calc
    dist ((H.interpolatedWalk p ε ω) (min t s))
        ((H.interpolatedWalk q ε ω) (min t u)) ≤
      dist ((H.interpolatedWalk p ε ω) (min t s))
        ((H.interpolatedWalk p ε ω) (min t u)) +
      dist ((H.interpolatedWalk p ε ω) (min t u))
        ((H.interpolatedWalk q ε ω) (min t u)) := dist_triangle _ _ _
    _ ≤ 2 * (ε : ℝ) * L + (ε : ℝ) * r :=
      add_le_add hp (dist_interpolatedWalk_le_of_dist_representatives_le H p q ω
        hpos hunb hclose ε (min t u))

end LatticeProb.CellConfigInterpolation
end

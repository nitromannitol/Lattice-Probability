import LatticeProb.Walk.CellConfigRepresentativeDistance
import LatticeProb.Walk.CellConfigEdgeOscillation

/-! # Stopped interpolations with different representatives -/

set_option autoImplicit false

noncomputable section

open ReflectedGMS ReflectedGMS.GMS
open scoped NNReal

namespace LatticeProb.CellConfigInterpolation

/-- If two stopping times lie on one edge of the same holding-time clock, the
stopped interpolations differ by at most the scaled representative error plus
the scaled distance between the edge endpoints. -/
theorem dist_stopped_interpolatedWalk_le_of_representatives_close
    (H : CellConfig) (p q : H.cells → Plane) (ω : ℕ → H.cells)
    (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    {r : ℝ} (hclose : ∀ K, dist (p K) (q K) ≤ r)
    {ε : ℝ≥0} (hε : 0 < ε) (n : ℕ) (s u : ℝ≥0)
    (hs₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (s : ℝ))
    (hs₂ : (s : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (hu₁ : (ε : ℝ) ^ 2 * H.jumpTime ω n ≤ (u : ℝ))
    (hu₂ : (u : ℝ) ≤ (ε : ℝ) ^ 2 * H.jumpTime ω (n + 1))
    (t : ℝ≥0) :
    dist ((H.interpolatedWalk p ε ω) (min t s))
      ((H.interpolatedWalk q ε ω) (min t u)) ≤
      (ε : ℝ) * dist (p (ω n)) (p (ω (n + 1))) + (ε : ℝ) * r := by
  calc
    dist ((H.interpolatedWalk p ε ω) (min t s))
        ((H.interpolatedWalk q ε ω) (min t u)) ≤
      dist ((H.interpolatedWalk p ε ω) (min t s))
          ((H.interpolatedWalk p ε ω) (min t u)) +
        dist ((H.interpolatedWalk p ε ω) (min t u))
          ((H.interpolatedWalk q ε ω) (min t u)) := dist_triangle _ _ _
    _ ≤ (ε : ℝ) * dist (p (ω n)) (p (ω (n + 1))) + (ε : ℝ) * r :=
      add_le_add (dist_stopped_interpolatedWalk_le_edge H p ω hpos hunb hε n s u
        hs₁ hs₂ hu₁ hu₂ t)
        (dist_interpolatedWalk_le_of_dist_representatives_le H p q ω hpos hunb hclose ε
          (min t u))

end LatticeProb.CellConfigInterpolation
end

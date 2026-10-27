import LatticeProb.Prob.Percolation.LatticeClusterBall


/-!
# Green columns on open components

The predicate records the unit-pole equation and the dimension-dependent behavior
at infinity on an entire open component. It does not select a Green function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

namespace LatticeProb.Percolation

noncomputable section

/-- The Green column characterized by its unit-neighbor Laplacian and its
normalization at Euclidean infinity. -/
def IsGreenColumn (d : ℕ) (_hd : 2 ≤ d) {ω : Configuration d}
    (C : OpenComponent ω) (y : C) (g : C → ℝ) : Prop :=
  (∀ x : C, -componentLaplacian C g x = if x = y then 1 else 0) ∧
  (d = 2 → g y = 0 ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ x : C, R ≤ ‖latticeEuclideanEmbedding x.val‖ →
        |g x| ≤ ε * ‖latticeEuclideanEmbedding x.val‖) ∧
  (3 ≤ d → ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ x : C, R ≤ ‖latticeEuclideanEmbedding x.val‖ → |g x| ≤ ε)

end
end LatticeProb.Percolation

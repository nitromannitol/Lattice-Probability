import LatticeProb.Walk.EventualIndexedBallContainment

/-! # Ball containment on a common tail -/

set_option autoImplicit false

open Set Metric Filter

namespace LatticeProb

/-- A common tail makes both preimage containments hold at every index, while
preserving eventual uniform closeness of the two position maps. -/
theorem exists_shift_indexedBall_preimages_subset_outer {E J : Type*}
    [MetricSpace E] [ProperSpace E] [Fintype J] (V : ℕ → Type*)
    (center : J → E) (r : J → ℝ) {W : Set E} (hW : IsOpen W)
    (hballs : ∀ j, closedBall (center j) (r j) ⊆ W)
    (p q : ∀ n, V n → E)
    (hclose : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v,
      dist (p n v) (q n v) < δ) :
    ∃ N : ℕ,
      (∀ n j, (p (n + N)) ⁻¹' ball (center j) (r j) ⊆ (p (n + N)) ⁻¹' W ∧
        (q (n + N)) ⁻¹' ball (center j) (r j) ⊆ (p (n + N)) ⁻¹' W) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ v,
        dist (p (n + N) v) (q (n + N) v) < δ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_indexedBall_preimages_subset_outer atTop V center r hW hballs p q hclose)
  refine ⟨N, ?_, ?_⟩
  · intro n j
    exact hN (n + N) (Nat.le_add_left N n) j
  · intro δ hδ
    exact (tendsto_add_atTop_nat N).eventually (hclose δ hδ)

end LatticeProb

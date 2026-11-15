import LatticeProb.Prob.SelectorInitialCell

/-! # Initial endpoint estimates at selected starting points -/

set_option autoImplicit false

open Set Metric Filter BouRabeeGwynne

namespace LatticeProb

/-- An eventual endpoint estimate holds simultaneously at every active vertex
when the comparison starts at the vertex position itself. -/
theorem eventually_selected_same_start_endpoint_estimate
    {X J ι κ : Type*} [PseudoMetricSpace X]
    (E : ι → Set X) (choice : ι → Option J) (D : Set X) (I : J → Set X)
    (a δ b : ℝ) (hδ : 0 ≤ δ)
    (hactive : ∀ x ∈ D, cellSelector E choice x ≠ none)
    (hdisj : Pairwise (fun k l => Disjoint (E k) (E l)))
    (hinside : ∀ k j, choice k = some j → E k ⊆ I j)
    (hdiam : ∀ k, ∀ x ∈ E k, ∀ y ∈ E k, dist x y ≤ a)
    (V : ℕ → Type*) (q : ∀ n, V n → X)
    (error : ∀ n, J → V n → X → κ → ℝ)
    (herror : ∀ᶠ n in atTop, ∀ j (v : V n) y,
      q n v ∈ I j → y ∈ I j → dist (q n v) y ≤ δ →
      ∀ k, |error n j v y k| ≤ b) :
    ∀ᶠ n in atTop, ∀ v : V n, q n v ∈ D →
      ∃ j, cellSelector E choice (q n v) = some j ∧ q n v ∈ I j ∧
        ∀ k, |error n j v (q n v) k| ≤ b := by
  filter_upwards [herror] with n hn
  intro v hv
  obtain ⟨k, j, hj, _, _, hq, _⟩ :=
    exists_selected_cell_initial_points E choice D I a hactive hdisj hinside hdiam hv
  exact ⟨j, hj, hq, hn j v (q n v) hq hq (by simpa using hδ)⟩

end LatticeProb

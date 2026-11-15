import LatticeProb.Prob.SelectorInitialCell

/-! # Endpoint estimates for starts in a selected cell -/

set_option autoImplicit false

open Set Metric Filter BouRabeeGwynne

namespace LatticeProb

/-- An eventual endpoint estimate applies to all comparison starts in the
selected cell, provided its diameter is within the estimate's tolerance. -/
theorem eventually_selected_cell_start_endpoint_estimate
    {X J ι κ : Type*} [PseudoMetricSpace X]
    (E : ι → Set X) (choice : ι → Option J) (D : Set X) (I : J → Set X)
    (a δ b : ℝ) (haδ : a ≤ δ)
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
      ∃ (i : ι) (j : J), cellSelector E choice (q n v) = some j ∧
        q n v ∈ E i ∧ q n v ∈ I j ∧ ∀ y ∈ E i,
          cellSelector E choice y = some j ∧ y ∈ I j ∧
            ∀ k, |error n j v y k| ≤ b := by
  filter_upwards [herror] with n hn
  intro v hv
  obtain ⟨i, j, hj, _, hqi, hq, hy⟩ :=
    exists_selected_cell_initial_points E choice D I a hactive hdisj hinside hdiam hv
  refine ⟨i, j, hj, hqi, hq, ?_⟩
  intro y hyi
  obtain ⟨hsel, hyj, hdist⟩ := hy y hyi
  exact ⟨hsel, hyj, hn j v y hq hyj (hdist.trans haδ)⟩

end LatticeProb

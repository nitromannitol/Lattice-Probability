import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector

/-! # Extending finite families of cell selectors -/

set_option autoImplicit false

open Set Metric BouRabeeGwynne

namespace LatticeProb

/-- Repeating the last finite-indexed selector gives an all-indexed family with
its measurable cells, coverage and margin intact. -/
theorem finite_horizon_cell_selectors_extend
    {X J : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [MeasurableSpace (Option J)] (L : ℕ)
    (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set X)
    (choice : ∀ i, Fin (m i) → Option J) (W : J → Set X)
    (D T : Set X) (margin a : ℝ)
    (hdisj : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
    (hmeas : ∀ i k, MeasurableSet (E i k))
    (hdiam : ∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hinside : ∀ i k j, choice i k = some j → E i k ⊆ W j)
    (hcover : ∀ i j, closure (W j) ⊆ ⋃ k, E i k)
    (hselect : ∀ i, Measurable (cellSelector (E i) (choice i)))
    (hactive : ∀ i x, x ∈ D → cellSelector (E i) (choice i) x ≠ none)
    (hmargin : ∀ i x j, cellSelector (E i) (choice i) x = some j →
      ball x (margin / 2) ⊆ W j)
    (hTD : T ⊆ D) :
    let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
    let m' : ℕ → ℕ := fun t => m (ix t)
    let E' : ∀ t, Fin (m' t) → Set X := fun t => E (ix t)
    let choice' : ∀ t, Fin (m' t) → Option J := fun t => choice (ix t)
    (∀ t, Pairwise (fun k l => Disjoint (E' t k) (E' t l))) ∧
    (∀ t k, MeasurableSet (E' t k)) ∧
    (∀ t k, ∀ x ∈ E' t k, ∀ y ∈ E' t k, dist x y ≤ a) ∧
    (∀ t k j, choice' t k = some j → E' t k ⊆ W j) ∧
    (∀ t j, closure (W j) ⊆ ⋃ k, E' t k) ∧
    (∀ t, Measurable (cellSelector (E' t) (choice' t))) ∧
    (∀ t x j, cellSelector (E' t) (choice' t) x = some j →
      ball x (margin / 2) ⊆ W j) ∧
    (∀ t x, cellSelector (E' t) (choice' t) x = none → x ∉ T) := by
  dsimp only
  refine ⟨fun t => hdisj _, fun t => hmeas _, fun t => hdiam _,
    fun t => hinside _, fun t => hcover _, fun t => hselect _,
    fun t => hmargin _, ?_⟩
  intro t x hn hx
  exact hactive _ x (hTD hx) hn

end LatticeProb

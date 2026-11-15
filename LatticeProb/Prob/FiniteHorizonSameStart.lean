import LatticeProb.Prob.FiniteHorizonSelectorExtension
import LatticeProb.Prob.SelectorSameStartEndpoints

/-! # Finite-horizon selectors and initial endpoint estimates -/

set_option autoImplicit false

open Set Metric Filter BouRabeeGwynne

namespace LatticeProb

/-- A finite selector family extends to all indices, while its initial selector
admits the supplied eventual endpoint estimate at each active vertex itself. -/
theorem finite_horizon_selectors_with_same_start_estimate
    {X J κ : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [MeasurableSpace (Option J)] (L : ℕ)
    (m : Fin (L + 1) → ℕ) (E : ∀ i, Fin (m i) → Set X)
    (choice : ∀ i, Fin (m i) → Option J) (W I : J → Set X)
    (D T : Set X) (margin a δ b : ℝ) (hδ : 0 ≤ δ)
    (hdisj : ∀ i, Pairwise (fun k l => Disjoint (E i k) (E i l)))
    (hmeas : ∀ i k, MeasurableSet (E i k))
    (hdiam : ∀ i k, ∀ x ∈ E i k, ∀ y ∈ E i k, dist x y ≤ a)
    (hinside : ∀ i k j, choice i k = some j → E i k ⊆ W j)
    (hinner : ∀ i k j, choice i k = some j → E i k ⊆ I j)
    (hcover : ∀ i j, closure (W j) ⊆ ⋃ k, E i k)
    (hselect : ∀ i, Measurable (cellSelector (E i) (choice i)))
    (hactive : ∀ i x, x ∈ D → cellSelector (E i) (choice i) x ≠ none)
    (hmargin : ∀ i x j, cellSelector (E i) (choice i) x = some j →
      ball x (margin / 2) ⊆ W j)
    (hTD : T ⊆ D)
    (V : ℕ → Type*) (q : ∀ n, V n → X)
    (error : ∀ n, J → V n → X → κ → ℝ)
    (herror : ∀ᶠ n in atTop, ∀ j (v : V n) y,
      q n v ∈ I j → y ∈ I j → dist (q n v) y ≤ δ →
      ∀ k, |error n j v y k| ≤ b) :
    let ix : ℕ → Fin (L + 1) := fun t => ⟨min t L, Nat.lt_succ_of_le (min_le_right _ _)⟩
    let m' : ℕ → ℕ := fun t => m (ix t)
    let E' : ∀ t, Fin (m' t) → Set X := fun t => E (ix t)
    let choice' : ∀ t, Fin (m' t) → Option J := fun t => choice (ix t)
    ((∀ t, Pairwise (fun k l => Disjoint (E' t k) (E' t l))) ∧
    (∀ t k, MeasurableSet (E' t k)) ∧
    (∀ t k, ∀ x ∈ E' t k, ∀ y ∈ E' t k, dist x y ≤ a) ∧
    (∀ t k j, choice' t k = some j → E' t k ⊆ W j) ∧
    (∀ t j, closure (W j) ⊆ ⋃ k, E' t k) ∧
    (∀ t, Measurable (cellSelector (E' t) (choice' t))) ∧
    (∀ t x j, cellSelector (E' t) (choice' t) x = some j →
      ball x (margin / 2) ⊆ W j) ∧
    (∀ t x, cellSelector (E' t) (choice' t) x = none → x ∉ T)) ∧
    (∀ᶠ n in atTop, ∀ v : V n, q n v ∈ D →
      ∃ j, cellSelector (E' 0) (choice' 0) (q n v) = some j ∧
        q n v ∈ I j ∧ ∀ k, |error n j v (q n v) k| ≤ b) := by
  dsimp only
  refine ⟨finite_horizon_cell_selectors_extend L m E choice W D T margin a
    hdisj hmeas hdiam hinside hcover hselect hactive hmargin hTD, ?_⟩
  exact eventually_selected_same_start_endpoint_estimate _ _ D I a δ b hδ
    (hactive _) (hdisj _) (hinner _) (hdiam _) V q error herror

end LatticeProb

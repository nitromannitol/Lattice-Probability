import LatticeProb.Prob.FiniteHorizonSameStart

/-! # Joint endpoint estimates for finite-horizon selectors -/

set_option autoImplicit false

open Set Metric Filter BouRabeeGwynne

namespace LatticeProb

/-- The supplied joint transition and initial estimates hold for a selected
vertex when the comparison starts at the vertex itself. -/
theorem finite_horizon_selectors_with_joint_same_start_estimate
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
    (V : ℕ → Type*) (q : ∀ n, V n → X) (step : ℕ → Prop)
    (error : ∀ n, J → V n → X → κ → ℝ)
    (hjoint : ∀ᶠ n in atTop, ∀ j (v : V n) y,
      q n v ∈ I j → y ∈ I j → dist (q n v) y ≤ δ →
      step n ∧ ∀ k, |error n j v y k| ≤ b) :
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
        q n v ∈ I j ∧ step n ∧ ∀ k, |error n j v (q n v) k| ≤ b) := by
  have herror : ∀ᶠ n in atTop, ∀ j (v : V n) y,
      q n v ∈ I j → y ∈ I j → dist (q n v) y ≤ δ →
      ∀ k, |error n j v y k| ≤ b := by
    filter_upwards [hjoint] with n hn
    intro j v y hv hy hdist
    exact (hn j v y hv hy hdist).2
  obtain ⟨hgeometry, hinitial⟩ :=
    finite_horizon_selectors_with_same_start_estimate L m E choice W I D T margin a δ b hδ
      hdisj hmeas hdiam hinside hinner hcover hselect hactive hmargin hTD V q error herror
  refine ⟨hgeometry, ?_⟩
  filter_upwards [hjoint, hinitial] with n hn hi
  intro v hv
  obtain ⟨j, hj, hq, he⟩ := hi v hv
  exact ⟨j, hj, hq, (hn j v (q n v) hq hq (by simpa using hδ)).1, he⟩

end LatticeProb

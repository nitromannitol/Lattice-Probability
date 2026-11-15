import LatticeProb.Prob.LocalizedMarkedRectangleMarginal

/-! Phase convergence for finite families of marked boxes. -/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace LatticeProb

/-- Finite weighted families of disjoint marked boxes have phase laws
converging to their first marginal paired with uniform cube measure. -/
theorem tendsto_tvDist_weighted_localized_marked_box_families_phase
    {E κ τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (ρ : Measure E) [IsFiniteMeasure ρ] (n : ℕ) (s : Finset κ)
    (c : κ → ℝ≥0∞) (hc : ∀ k ∈ s, c k ≠ ⊤)
    (F : κ → Finset (Set (E × (Fin n → ℝ)))) (p q : Fin n → ℝ)
    (hF : ∀ k ∈ s, (↑(F k) : Set (Set (E × (Fin n → ℝ)))) ⊆
      Set.image2 (· ×ˢ ·) {A : Set E | MeasurableSet A}
        (Set.univ.pi '' Set.univ.pi (fun _ : Fin n =>
          {S : Set ℝ | ∃ u v : ℝ, S = Ico u v})))
    (hd : ∀ k ∈ s, (↑(F k) : Set (Set (E × (Fin n → ℝ)))).PairwiseDisjoint id)
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    let μ := ∑ k ∈ s, c k • (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict (⋃ j ∈ F k, j))
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (μ.map (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
      ((μ.map Prod.fst).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  classical
  have hrepr (k : κ) (j : Set (E × (Fin n → ℝ))) :
      ∃ A : Set E, ∃ u v : Fin n → ℝ, MeasurableSet A ∧
        (k ∈ s → j ∈ F k → j = A ×ˢ univ.pi (fun i => Ico (u i) (v i))) := by
    by_cases h : k ∈ s ∧ j ∈ F k
    · obtain ⟨A, hA, S, ⟨f, hf, rfl⟩, hj⟩ := hF k h.1 h.2
      have hcoords : ∀ i, ∃ u v : ℝ, f i = Ico u v := by
        intro i
        exact hf i (mem_univ i)
      choose u v huv using hcoords
      refine ⟨A, u, v, hA, ?_⟩
      intro _ _
      have hf_eq : f = fun i => Ico (u i) (v i) := funext huv
      simpa only [hf_eq] using hj.symm
    · exact ⟨∅, 0, 0, MeasurableSet.empty, fun hk hj => (h ⟨hk, hj⟩).elim⟩
  choose A u v hA hbox using hrepr
  have hd' : ∀ k ∈ s, (↑(F k) : Set (Set (E × (Fin n → ℝ)))).PairwiseDisjoint
      (fun j => A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i))) := by
    intro k hk x hx y hy hxy
    change Disjoint (A k x ×ˢ univ.pi (fun i => Ico (u k x i) (v k x i)))
      (A k y ×ˢ univ.pi (fun i => Ico (u k y i) (v k y i)))
    rw [← hbox k x hk hx, ← hbox k y hk hy]
    exact hd k hk hx hy hxy
  have hu (k : κ) (hk : k ∈ s) :
      (⋃ j ∈ F k, A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i))) =
        ⋃ j ∈ F k, j := by
    apply iUnion_congr
    intro j
    apply iUnion_congr
    intro hj
    exact (hbox k j hk hj).symm
  have h := tendsto_tvDist_weighted_localized_marked_rectangles_phase ρ n s c hc F A u v p q
    hA hd' a ha θ hθ
  have hm := weighted_localized_marked_rectangles_marginal_prod ρ n s c F A u v p q hA hd'
  dsimp only at h hm ⊢
  rw [hm] at h
  have hsum : (∑ k ∈ s, c k • (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict
        (⋃ j ∈ F k, A k j ×ˢ univ.pi (fun i => Ico (u k j i) (v k j i))))) =
      ∑ k ∈ s, c k • (((ρ.prod (volume : Measure (Fin n → ℝ))).restrict
      (univ ×ˢ univ.pi (fun i => Ico (p i) (q i)))).restrict (⋃ j ∈ F k, j)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hu k hk]
  rw [hsum] at h
  exact h

end LatticeProb

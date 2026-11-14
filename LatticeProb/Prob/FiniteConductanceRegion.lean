import LatticeProb.Prob.FiniteConductanceRestriction

/-! # Finite regions of conductance networks

A finite active set with finite conductance neighborhoods has a smallest region
containing the active set, its neighbors, and a specified starting vertex.
-/

set_option autoImplicit false

namespace LatticeProb

variable {V : Type*} (c : V → V → ℝ)

/-- The active set together with its conductance neighbors and a starting vertex. -/
def conductanceRegion (A : Set V) (start : V) : Set V :=
  (A ∪ {w | ∃ v ∈ A, c v w ≠ 0}) ∪ {start}

/-- A finite active set with finite neighborhoods has a finite conductance region. -/
theorem conductanceRegion_finite (A : Set V) (start : V) (hA : A.Finite)
    (hneighbors : ∀ v ∈ A, {w | c v w ≠ 0}.Finite) :
    (conductanceRegion c A start).Finite := by
  have hN : {w | ∃ v ∈ A, c v w ≠ 0}.Finite := by
    convert Set.Finite.biUnion hA hneighbors using 1
    ext w
    simp
  exact (hA.union hN).union (Set.finite_singleton start)

/-- The conductance region is the least set containing the active set, its
nonzero conductance neighbors, and the starting vertex. -/
theorem conductanceRegion_subset_iff (A R : Set V) (start : V) :
    conductanceRegion c A start ⊆ R ↔
      A ⊆ R ∧ start ∈ R ∧ ∀ v ∈ A, ∀ w, c v w ≠ 0 → w ∈ R := by
  constructor
  · intro h
    refine ⟨fun v hv => h (Or.inl (Or.inl hv)), h (Or.inr rfl), ?_⟩
    intro v hv w hw
    exact h (Or.inl (Or.inr ⟨v, hv, hw⟩))
  · rintro ⟨hA, hstart, hneighbors⟩ w (hw | hw)
    · rcases hw with hw | ⟨v, hv, hvw⟩
      · exact hA hw
      · exact hneighbors v hv w hvw
    · rcases hw with rfl
      exact hstart

/-- No conductance from an active vertex is lost outside its conductance region. -/
theorem conductanceRegion_eq_zero_of_not_mem (A : Set V) (start v w : V)
    (hv : v ∈ A) (hw : w ∉ conductanceRegion c A start) : c v w = 0 := by
  by_contra hn
  exact hw (Or.inl (Or.inr ⟨v, hv, hn⟩))

/-- The restricted walk has the ambient transition at every active vertex. -/
theorem conductanceRegion_transition
    (hsymm : ∀ v w, c v w = c w v)
    (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
    (A : Set V) (start : V) [Fintype (conductanceRegion c A start)]
    (v w : conductanceRegion c A start) (hv : (v : V) ∈ A) :
    (finiteConductanceRestriction c hsymm hnonneg hloop
      (conductanceRegion c A start)).transitionProbability
        (Subtype.val ⁻¹' A) v w = c v w / (∑' z, c v z) :=
  finiteConductanceRestriction_transition c hsymm hnonneg hloop _ _ v w hv
    (fun z hz => conductanceRegion_eq_zero_of_not_mem c A start v z hv hz)

end LatticeProb

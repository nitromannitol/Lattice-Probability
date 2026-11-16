import LatticeProb.Probability.Percolation.FirstContactSupport

/-!
# First contact and the left component

A first-contact witness stays in the component of the square outside the
barrier reached from its left boundary. Its edges give a finite support.
-/

namespace EdgeCrossing

open MeasureTheory ProbabilityTheory Percolation.Literature SimpleGraph

noncomputable section

private abbrev Edge := (LatticeModels.zdGraph 2).edgeSet
private abbrev Config := Edge → Prop

/-- Vertices connected to the left boundary inside the square off the barrier. -/
def firstContactComponent (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) : Set (LatticeModels.Site 2) :=
  {z | ∃ t ∈ outerLeft n, ∃ p : (LatticeModels.zdGraph 2).Walk t z,
    ∀ x ∈ p.support, x ∈ centeredSquare n ∧
      x ∉ Q.support ∧ reflY 0 x ∉ Q.support}

/-- First contact with the additional requirement that dart sources are in the left component. -/
def firstContactInComponent (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (reflected : Bool) : Set Config :=
  {ω | ∃ t ∈ outerLeft n, ∃ v ∈ (if reflected then
      {z | reflY 0 z ∈ Q.support} else {z | z ∈ Q.support}),
    ∃ p : (LatticeModels.zdGraph 2).Walk t v,
      (∀ z ∈ p.support, z ∈ centeredSquare n) ∧
      (∀ dart ∈ p.darts, dart.fst ∉ Q.support ∧ reflY 0 dart.fst ∉ Q.support) ∧
      (∀ dart ∈ p.darts, dart.fst ∈ firstContactComponent n Q) ∧
      ∀ e ∈ p.edges, e ∈ extend (LatticeModels.zdGraph 2) ω}

/-- The component condition is automatic, including for a walk with no edges. -/
theorem firstContact_eq_firstContactInComponent (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (reflected : Bool) :
    firstContact n Q reflected = firstContactInComponent n Q reflected := by
  classical
  ext ω
  constructor
  · rintro ⟨t, ht, v, hv, p, hp, ha, he⟩
    refine ⟨t, ht, v, hv, p, hp, ?_, ?_, he⟩
    · simpa only [Set.mem_ofPred_eq, not_or] using ha
    · intro dart hd
      have hz := p.dart_fst_mem_support_of_mem_darts hd
      have hzavoid : dart.fst ∉ Q.support ∧ reflY 0 dart.fst ∉ Q.support := by
        simpa only [Set.mem_ofPred_eq, not_or] using ha dart hd
      refine ⟨t, ht, p.takeUntil dart.fst hz, ?_⟩
      intro x hx
      refine ⟨hp x (p.support_takeUntil_subset_support hz hx), ?_⟩
      have hx' : x ∈ (p.takeUntil dart.fst hz).darts.map (·.fst) ++ [dart.fst] := by
        simpa only [Walk.map_fst_darts_append] using hx
      rcases List.mem_append.mp hx' with hx' | hx'
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx'
        have he' := p.darts_takeUntil_subset_darts hz he
        simpa only [Set.mem_ofPred_eq, not_or] using ha e he'
      · have : x = dart.fst := by simpa using hx'
        simpa [this] using hzavoid
  · rintro ⟨t, ht, v, hv, p, hp, ha, _, he⟩
    refine ⟨t, ht, v, hv, p, hp, ?_, he⟩
    intro dart hd
    simpa only [Set.mem_ofPred_eq, not_or] using ha dart hd

/-- Square edges with at least one endpoint in the left component. -/
def firstContactComponentEdges (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) : Finset Edge := by
  classical
  exact ((centeredSquare n).sym2.filter fun e => ∃ z ∈ e, z ∈ firstContactComponent n Q).subtype
    (fun e => e ∈ (LatticeModels.zdGraph 2).edgeSet)

/-- The component edge support consists exactly of square edges incident to the component. -/
theorem mem_firstContactComponentEdges_iff (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (e : Edge) :
    e ∈ firstContactComponentEdges n Q ↔
      (∀ z ∈ e.1, z ∈ centeredSquare n) ∧ ∃ z ∈ e.1, z ∈ firstContactComponent n Q := by
  classical
  simp [firstContactComponentEdges, Finset.mem_sym2_iff]

/-- Agreement on component edges preserves first-contact membership. -/
theorem firstContact_component_congr (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (reflected : Bool)
    (ω τ : Config) (h : ∀ e ∈ firstContactComponentEdges n Q, ω e = τ e) :
    ω ∈ firstContact n Q reflected ↔ τ ∈ firstContact n Q reflected := by
  classical
  rw [firstContact_eq_firstContactInComponent]
  suffices key : ∀ ω τ : Config,
      (∀ e ∈ firstContactComponentEdges n Q, ω e = τ e) →
      ω ∈ firstContactInComponent n Q reflected → τ ∈ firstContactInComponent n Q reflected by
    exact ⟨key ω τ h, key τ ω (fun e he => (h e he).symm)⟩
  intro ω τ h ⟨t, ht, v, hv, p, hp, ha, hc, he⟩
  refine ⟨t, ht, v, hv, p, hp, ha, hc, ?_⟩
  intro e hep
  have hedge := p.edges_subset_edgeSet hep
  have hT : (⟨e, hedge⟩ : Edge) ∈ firstContactComponentEdges n Q := by
    rw [mem_firstContactComponentEdges_iff]
    rw [Walk.edges, List.mem_map] at hep
    obtain ⟨dart, hdart, rfl⟩ := hep
    constructor
    · exact Finset.mem_sym2_iff.mp (Finset.mk_mem_sym2_iff.mpr
        ⟨hp _ (p.dart_fst_mem_support_of_mem_darts hdart),
          hp _ (p.dart_snd_mem_support_of_mem_darts hdart)⟩)
    · exact ⟨dart.fst, Sym2.mem_mk_left _ _, hc dart hdart⟩
  exact ⟨hedge, (h ⟨e, hedge⟩ hT).mp (he e hep).2⟩

/-- First contact is measurable using its component edge support. -/
theorem measurableSet_firstContact_component (n : ℕ) {c d : LatticeModels.Site 2}
    (Q : (LatticeModels.zdGraph 2).Walk c d) (reflected : Bool) :
    MeasurableSet (firstContact n Q reflected) := by
  exact LatticeProb.Prob.FiniteCellFactorization.measurableSet_event
    (fun e ω => ω e) (fun e => measurable_pi_apply e) (firstContactComponentEdges n Q) _
    (firstContact_component_congr n Q reflected)

end
end EdgeCrossing

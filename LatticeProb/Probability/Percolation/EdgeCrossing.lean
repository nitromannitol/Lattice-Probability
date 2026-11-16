import LatticeProb.Vendor.FormalMathPercolation.Literature.PlanarDuality

/-!
# Edge-indexed Bernoulli crossings

The edge-indexed product law gives the same horizontal crossing probabilities as the
ambient bond configuration law. The crossing is witnessed by a nearest-neighbor walk in
an inclusive rectangle, allowing the walk of length zero.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

variable {V : Type*} (G : SimpleGraph V) (p : unitInterval)

/-- Restrict a bond configuration to the edges of the graph. -/
def restrict (ω : BondConfig V) (e : G.edgeSet) : Prop := e.val ∈ ω

/-- Extend an edge configuration by closing all nonedges. -/
def extend (η : G.edgeSet → Prop) : BondConfig V :=
  {e | ∃ h : e ∈ G.edgeSet, η ⟨e, h⟩}

/-- Restriction to edge coordinates is measurable. -/
theorem measurable_restrict : Measurable (restrict G) := by
  change Measurable (fun ω (e : G.edgeSet) => e.val ∈ ω)
  fun_prop

/-- The restriction of the ambient law is the Bernoulli product on graph edges. -/
theorem edge_product_law :
    (bondPercolation G p).map (restrict G) =
      Measure.infinitePi (fun _ : G.edgeSet => bernoulliMeasure True False p) := by
  rw [bondPercolation, setBernoulli_eq_map, Measure.map_map]
  · convert (Measure.infinitePi_map_restrict' (μ := fun i : Sym2 V =>
      bernoulliMeasure (i ∈ G.edgeSet) False p) (I := G.edgeSet)) using 1
    · rfl
    · congr 1
      funext e
      simp only [e.property]
  · exact measurable_restrict G
  · fun_prop

/-- The ambient law is supported on graph edges. -/
theorem edge_support_ae [Countable V] :
    ∀ᵐ ω ∂bondPercolation G p, ω ∩ G.edgeSet = ω := by
  filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := G.edgeSet) (p := p)] with ω hω
  exact Set.inter_eq_self_of_subset_left hω

/-- Extension after restriction discards exactly the nonedges. -/
theorem extend_restrict (ω : BondConfig V) : extend G (restrict G ω) = ω ∩ G.edgeSet := by
  ext e
  simp [extend, restrict, and_comm]

/-- Edge configurations extended to pairs are supported on the edge set. -/
theorem extend_subset (η : G.edgeSet → Prop) : extend G η ⊆ G.edgeSet := by
  intro e he
  exact he.choose

/-- Extension by closed nonedges is measurable. -/
theorem measurable_extend : Measurable (extend G) := by
  apply Measurable.of_eval
  intro e
  change Measurable (fun η => e ∈ extend G η)
  by_cases he : e ∈ G.edgeSet
  · have h : (fun η => e ∈ extend G η) = (fun η => η ⟨e, he⟩) := by
      funext η
      simp [extend, he]
    rw [h]
    exact measurable_pi_apply (⟨e, he⟩ : G.edgeSet)
  · have h : (fun η => e ∈ extend G η) = (fun _ => False) := by
      funext η
      simp [extend, he]
    rw [h]
    exact measurable_const

variable (m n : ℕ)

/-- Horizontal crossing by an open nearest-neighbor walk within the inclusive rectangle. -/
def crossing : Set ((LatticeModels.zdGraph 2).edgeSet → Prop) :=
  {η | ∃ x ∈ leftSide m n, ∃ y ∈ rightSide m n,
    ∃ q : (LatticeModels.zdGraph 2).Walk x y,
      (∀ z ∈ q.support, z ∈ rectangle m n) ∧
      ∀ (e) (he : e ∈ q.edges), η ⟨e, q.edges_subset_edgeSet he⟩}

/-- Extension identifies the edge-indexed walk event with the ambient crossing. -/
theorem mem_crossing_iff (η : (LatticeModels.zdGraph 2).edgeSet → Prop) :
    η ∈ crossing m n ↔ extend (LatticeModels.zdGraph 2) η ∈ lrCrossing m n := by
  constructor
  · rintro ⟨x, hx, y, hy, q, hq, ho⟩
    refine ⟨x, hx, y, hy, mem_openConnIn_of_walk q hq ?_⟩
    intro e he
    exact ⟨q.edges_subset_edgeSet he, ho e he⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨q, hq, ho⟩ := exists_walk_of_mem_openConnIn (extend_subset _ _) hxy
    refine ⟨x, hx, y, hy, q, hq, ?_⟩
    intro e he
    exact (ho e he).choose_spec

/-- The source crossing is measurable for the edge-coordinate product σ-algebra. -/
theorem measurableSet_crossing : MeasurableSet (crossing m n) := by
  have heq : crossing m n = extend (LatticeModels.zdGraph 2) ⁻¹' lrCrossing m n := by
    ext η
    exact mem_crossing_iff m n η
  rw [heq]
  exact (measurableSet_openCrossing _ _ _).preimage (measurable_extend _)

/-- The source edge-product crossing probability equals the vendor probability. -/
theorem crossing_probability (p : unitInterval) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (crossing m n) = crossingProb p m n := by
  rw [← edge_product_law (LatticeModels.zdGraph 2) p, measureReal_def,
    Measure.map_apply (measurable_restrict _) (measurableSet_crossing m n)]
  rw [crossingProb, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [edge_support_ae (LatticeModels.zdGraph 2) p] with ω hω
  apply propext
  change (restrict (LatticeModels.zdGraph 2) ω ∈ crossing m n) ↔ ω ∈ lrCrossing m n
  rw [mem_crossing_iff, extend_restrict, hω]

end EdgeCrossing

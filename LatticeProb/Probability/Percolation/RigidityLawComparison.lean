import LatticeProb.Probability.Percolation.RigidityCrossingAdapter

/-!
# Square-lattice percolation law and critical probability

The Boolean bond model from Lattice-Probability revision
`7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069` and the ambient bond model
have the same percolation probability on the square lattice.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace RigidityLawComparison

open RigidityCrossingAdapter DualDecayRectangle

namespace Hist

/-- The infinite component event, as in `LatticeBondInfiniteEvent.lean` at revision
`7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`, lines 75–77. -/
def infiniteComponentEvent {d : ℕ} (x : RigidityCrossingAdapter.Hist.Vertex d) :
    Set (RigidityCrossingAdapter.Hist.Configuration d) :=
  {ω | ((RigidityCrossingAdapter.Hist.openGraph ω).connectedComponentMk x).supp.Infinite}

/-- The percolation probability, as in `LatticeBondInfiniteEvent.lean` at revision
`7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`, lines 124–126. -/
def theta (d : ℕ) (p : unitInterval) : ℝ :=
  (RigidityCrossingAdapter.Hist.latticeBondLaw d p).real (infiniteComponentEvent 0)

/-- The critical probability, as in `LatticeBondCritical.lean` at revision
`7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`, lines 36–38. -/
def criticalProbability (d : ℕ) [NeZero d] : ℝ :=
  sInf {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < theta d p}

end Hist

/-- Extending Boolean configurations gives the ambient bond law. -/
theorem map_law (p : unitInterval) :
    (RigidityCrossingAdapter.Hist.latticeBondLaw 2 p).map
      (EdgeCrossing.extend (LatticeModels.zdGraph 2) ∘ toEdgeConfig) =
        bondPercolation (LatticeModels.zdGraph 2) p := by
  rw [← Measure.map_map (EdgeCrossing.measurable_extend _) (by unfold toEdgeConfig; fun_prop)]
  rw [pinned_law_eq, map_bool_product_eq_restrict,
    Measure.map_map (EdgeCrossing.measurable_extend _) (EdgeCrossing.measurable_restrict _)]
  calc
    _ = (bondPercolation (LatticeModels.zdGraph 2) p).map id := by
      apply Measure.map_congr
      filter_upwards [EdgeCrossing.edge_support_ae (LatticeModels.zdGraph 2) p] with ω hω
      exact (EdgeCrossing.extend_restrict _ ω).trans hω
    _ = _ := Measure.map_id

/-- The component support and the reachable cluster are the same set. -/
theorem component_supp_eq_cluster {V : Type*} (G : SimpleGraph V) (x : V) :
    (G.connectedComponentMk x).supp = {y | G.Reachable x y} := by
  ext y
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, Set.mem_ofPred_eq]
  exact ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

/-- The two infinite-cluster events agree for every Boolean configuration. -/
theorem infinite_event_iff (ω : RigidityCrossingAdapter.Hist.Configuration 2) :
    ω ∈ Hist.infiniteComponentEvent 0 ↔
      (EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω)) ∈ percolatesAt 0 := by
  change ((RigidityCrossingAdapter.Hist.openGraph ω).connectedComponentMk 0).supp.Infinite ↔
    (openCluster (EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω)) 0).Infinite
  rw [component_supp_eq_cluster, ← open_graph_eq]
  rfl

/-- The pinned and ambient square-lattice percolation probabilities coincide. -/
theorem theta_eq (p : unitInterval) :
    Hist.theta 2 p = theta (LatticeModels.zdGraph 2) 0 p := by
  unfold Hist.theta theta
  have he : Hist.infiniteComponentEvent (0 : RigidityCrossingAdapter.Hist.Vertex 2) =
      (EdgeCrossing.extend (LatticeModels.zdGraph 2) ∘ toEdgeConfig) ⁻¹' percolatesAt 0 := by
    ext ω
    exact infinite_event_iff ω
  rw [he, ← map_measureReal_apply
    ((EdgeCrossing.measurable_extend _).comp (by unfold toEdgeConfig; fun_prop))
    (measurableSet_percolatesAt_holds 0), map_law]

/-- The positive-parameter sets agree. -/
theorem positive_parameter_set_eq :
    {q : ℝ | ∃ p : unitInterval, (p : ℝ) = q ∧ 0 < Hist.theta 2 p} =
      {q : ℝ | ∃ h : q ∈ unitInterval,
        0 < theta (LatticeModels.zdGraph 2) 0 ⟨q, h⟩} := by
  ext q
  constructor
  · rintro ⟨p, rfl, hp⟩
    exact ⟨p.property, by simpa only [← theta_eq] using hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨q, h⟩, rfl, by simpa only [theta_eq] using hp⟩

/-- The two critical probabilities coincide, including the endpoint convention. -/
theorem criticalProbability_eq :
    Hist.criticalProbability 2 = criticalProb (LatticeModels.zdGraph 2) 0 := by
  have h1 : (1 : ℝ) ∈ {q : ℝ | ∃ h : q ∈ unitInterval,
      0 < theta (LatticeModels.zdGraph 2) 0 ⟨q, h⟩} := by
    refine ⟨(1 : unitInterval).property, ?_⟩
    exact Kesten1980_theta_pos_holds 1 (by norm_num)
  unfold Hist.criticalProbability criticalProb
  rw [positive_parameter_set_eq, Set.union_eq_left.mpr]
  rintro q rfl
  exact h1

/-- The pinned square-lattice critical probability is one half. -/
theorem criticalProbability_eq_half : Hist.criticalProbability 2 = 1 / 2 := by
  rw [criticalProbability_eq, kesten_criticalProb_Z2_holds]

/-- The pinned rectangle crossing estimate holds above its critical probability. -/
theorem consumer_at_criticalProbability :
    Consumer.KestenRectangleCrossingAt (Hist.criticalProbability 2) := by
  rw [criticalProbability_eq_half]
  exact consumer_at_half

end RigidityLawComparison

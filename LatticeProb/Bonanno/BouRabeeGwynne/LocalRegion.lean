/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.LocalRegion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.LocalGeometry

namespace BouRabeeGwynne

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- `V[U]` from the paper. -/
def interiorVertices (U : Set (Euc d)) : Set T.V :=
  {v | T.pos v ∈ U}

/-- Neighbors of one tiling vertex. -/
def neighbors (v : T.V) : Set T.V :=
  {w | T.adj v w}

/-- `∂A`: vertices outside `A` which share an edge with a vertex of `A`. -/
def vertexBoundary (A : Set T.V) : Set T.V :=
  {w | w ∉ A ∧ ∃ v ∈ A, T.adj v w}

/-- `∂V[U]`. -/
def boundaryVertices (U : Set (Euc d)) : Set T.V :=
  T.vertexBoundary (T.interiorVertices U)

/-- `\bar A = A ∪ ∂A`. -/
def closedVertexSet (A : Set T.V) : Set T.V :=
  A ∪ T.vertexBoundary A

/-- `\bar V[U]`. -/
def closedVertices (U : Set (Euc d)) : Set T.V :=
  T.closedVertexSet (T.interiorVertices U)

/-- A vertex whose cell lies in the ambient set has finitely many neighbors. -/
theorem neighbors_finite (v : T.V) (hv : (T.cell v).carrier ⊆ T.domain) :
    (T.neighbors v).Finite := by
  have hloc := T.toTilingData.locallyFinite (T.cell v).carrier (T.cell v).compact
    hv
  apply hloc.subset
  intro w hw
  change T.adj v w at hw
  rcases hw.2.1 with ⟨x, hxv, hxw⟩
  exact ⟨x, hxw, hxv⟩

/-- The finite finset of graph neighbors of `v`. -/
noncomputable def neighborFinset (v : T.V) (hv : (T.neighbors v).Finite) : Finset T.V :=
  hv.toFinset

@[simp] lemma mem_neighborFinset {v w : T.V} (hv : (T.neighbors v).Finite) :
    w ∈ T.neighborFinset v hv ↔ T.adj v w := by
  classical
  simp [neighborFinset, neighbors]

/--
A bounded set whose closure is contained in the tiling domain contains only
finitely many tiling vertices.  This is the local finiteness hypothesis exactly
in the form used in Sections 2 and 3.
-/
theorem interiorVertices_finite {U : Set (Euc d)} (hU : Bornology.IsBounded U)
    (hUD : closure U ⊆ T.domain) :
    (T.interiorVertices U).Finite := by
  have hK : IsCompact (closure U) := hU.isCompact_closure
  have hloc := T.toTilingData.locallyFinite (closure U) hK hUD
  apply hloc.subset
  intro v hv
  change T.pos v ∈ U at hv
  refine ⟨T.pos v, ?_, subset_closure hv⟩
  exact interior_subset (T.toTilingData.pos_mem_interior v)

/-- A finite set of vertices has a finite external vertex boundary. -/
theorem vertexBoundary_finite {A : Set T.V} (hA : A.Finite)
    (hneighbors : ∀ v ∈ A, (T.neighbors v).Finite) :
    (T.vertexBoundary A).Finite := by
  have hUnion : (⋃ v ∈ A, T.neighbors v).Finite :=
    Set.Finite.biUnion hA hneighbors
  apply hUnion.subset
  intro w hw
  rcases hw.2 with ⟨v, hvA, hvw⟩
  exact Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hvA, hvw⟩⟩

/-- For relatively compact bounded `U`, the paper's boundary vertex set is finite. -/
theorem boundaryVertices_finite {U : Set (Euc d)} (hU : Bornology.IsBounded U)
    (hUD : closure U ⊆ T.domain)
    (hcells : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ T.domain) :
    (T.boundaryVertices U).Finite :=
  T.vertexBoundary_finite (T.interiorVertices_finite hU hUD)
    (fun v hv => T.neighbors_finite v (hcells v hv))

/-- For relatively compact bounded `U`, `\bar V[U]` is finite. -/
theorem closedVertices_finite {U : Set (Euc d)} (hU : Bornology.IsBounded U)
    (hUD : closure U ⊆ T.domain)
    (hcells : ∀ v ∈ T.interiorVertices U, (T.cell v).carrier ⊆ T.domain) :
    (T.closedVertices U).Finite := by
  exact (T.interiorVertices_finite hU hUD).union
    (T.boundaryVertices_finite hU hUD hcells)

/-- A boundary vertex is outside `U` and adjacent to an interior vertex. -/
lemma mem_boundaryVertices_iff {U : Set (Euc d)} {w : T.V} :
    w ∈ T.boundaryVertices U ↔
      T.pos w ∉ U ∧ ∃ v : T.V, T.pos v ∈ U ∧ T.adj v w := by
  rfl

/-- Every interior vertex belongs to `\bar V[U]`. -/
lemma interiorVertices_subset_closedVertices (U : Set (Euc d)) :
    T.interiorVertices U ⊆ T.closedVertices U := by
  intro v hv
  exact Or.inl hv

/-- Every neighbor of an interior vertex lies in `\bar V[U]`. -/
lemma neighbor_mem_closedVertices {U : Set (Euc d)} {v w : T.V}
    (hv : v ∈ T.interiorVertices U) (hvw : T.adj v w) :
    w ∈ T.closedVertices U := by
  by_cases hw : w ∈ T.interiorVertices U
  · exact Or.inl hw
  · exact Or.inr ⟨hw, v, hv, hvw⟩

/-- A sufficiently small mesh inside the collar gives a finite Dirichlet region. -/
theorem closedVertices_finite_of_collar {U : Set (Euc d)}
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U T.domain)
    {δ : ℝ} (hcollar : Metric.cthickening δ (closure U) ⊆ T.domain)
    (hmesh : T.mesh ≠ ⊤) (hδ : T.mesh.toReal ≤ δ) :
    (T.closedVertices U).Finite := by
  apply T.closedVertices_finite hU hUD.closure_subset
  intro v hv
  exact T.toTilingData.cell_subset_domain_of_collar hcollar hv hmesh hδ

/-- An exterior boundary vertex is within two meshes of an interior marked point. -/
lemma boundaryVertices_near_interior {U : Set (Euc d)} {w : T.V}
    (hw : w ∈ T.boundaryVertices U) (hmesh : T.mesh ≠ ⊤) :
    ∃ v : T.V, T.pos v ∈ U ∧ dist (T.pos w) (T.pos v) ≤ 2 * T.mesh.toReal := by
  obtain ⟨v, hv, hvw⟩ := hw.2
  refine ⟨v, hv, ?_⟩
  simpa only [dist_comm] using T.toTilingData.edge_dist_le_two_mesh hvw hmesh

/-- Both the interior and external boundary lie in the two-mesh collar. -/
lemma closedVertices_pos_mem_cthickening {U : Set (Euc d)} {w : T.V}
    (hw : w ∈ T.closedVertices U) (hmesh : T.mesh ≠ ⊤) :
    T.pos w ∈ Metric.cthickening (2 * T.mesh.toReal) (closure U) := by
  rcases hw with hw | hw
  · exact Metric.mem_cthickening_of_dist_le (T.pos w) (T.pos w) _ _
      (subset_closure hw) (by
        rw [dist_self]
        exact mul_nonneg zero_le_two ENNReal.toReal_nonneg)
  · obtain ⟨v, hv, hdist⟩ := T.boundaryVertices_near_interior hw hmesh
    exact Metric.mem_cthickening_of_dist_le (T.pos w) (T.pos v) _ _
      (subset_closure hv) hdist

end OrthogonalTiling

end BouRabeeGwynne

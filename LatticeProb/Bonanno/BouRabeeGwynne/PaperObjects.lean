/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.PaperObjects at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Topology.MetricSpace.Thickening

open scoped BigOperators ENNReal Topology MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne

/-- Euclidean `d`-space used throughout the paper. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A nonempty domain is an open connected set. -/
def IsDomain {d : ℕ} (D : Set (Euc d)) : Prop :=
  IsOpen D ∧ D.Nonempty ∧ IsPreconnected D

/-- The approved ambient collar around a domain under consideration. -/
def HasAmbientCollar {d : ℕ} (U D : Set (Euc d)) : Prop :=
  closure U ⊆ interior D

lemma HasAmbientCollar.closure_subset {d : ℕ} {U D : Set (Euc d)}
    (h : HasAmbientCollar U D) : closure U ⊆ D :=
  h.trans interior_subset

lemma HasAmbientCollar.subset {d : ℕ} {U D : Set (Euc d)}
    (h : HasAmbientCollar U D) : U ⊆ D :=
  subset_closure.trans h.closure_subset

/-- Compactness turns the ambient collar into a uniform positive neighborhood. -/
lemma HasAmbientCollar.exists_cthickening_subset {d : ℕ} {U D : Set (Euc d)}
    (h : HasAmbientCollar U D) (hU : IsCompact (closure U)) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ (closure U) ⊆ D := by
  obtain ⟨δ, hδ, hδD⟩ := hU.exists_cthickening_subset_open isOpen_interior h
  exact ⟨δ, hδ, hδD.trans interior_subset⟩

/--
A closed convex polytope.  The finite halfspace representation records the
polyhedral hypothesis; compactness records boundedness.
-/
structure ConvexPolytope (d : ℕ) : Type where
  carrier : Set (Euc d)
  compact : IsCompact carrier
  convex : Convex ℝ carrier
  interior_nonempty : (interior carrier).Nonempty
  halfspaces : Finset (Euc d × ℝ)
  halfspace_rep :
    carrier = {x | ∀ p ∈ halfspaces, inner ℝ p.1 x ≤ p.2}

/-- The Euclidean diameter of a polytope, as an extended nonnegative real. -/
noncomputable def ConvexPolytope.diamENN {d : ℕ} (P : ConvexPolytope d) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam P.carrier)

/-- Full-dimensional Euclidean volume. -/
noncomputable def ConvexPolytope.volume {d : ℕ} (P : ConvexPolytope d) : ℝ≥0∞ :=
  μHE[d] P.carrier

/-- A codimension-one nonempty intersection of two full-dimensional cells. -/
def IsCodimOneFacet {d : ℕ} (P Q : Set (Euc d)) : Prop :=
  (P ∩ Q).Nonempty ∧
    Module.finrank ℝ (affineSpan ℝ (P ∩ Q)).direction = d - 1

lemma IsCodimOneFacet.symm {d : ℕ} {P Q : Set (Euc d)}
    (h : IsCodimOneFacet P Q) : IsCodimOneFacet Q P := by
  unfold IsCodimOneFacet at *
  rw [Set.inter_comm Q P]
  exact h

/--
Local finiteness in the precise sense of Section 1.1: each compact subset of
`D` intersects only finitely many cells.
-/
def LocallyFiniteCells {d : ℕ} {V : Type*}
    (D : Set (Euc d)) (cell : V → ConvexPolytope d) : Prop :=
  ∀ K : Set (Euc d), IsCompact K → K ⊆ D →
    Set.Finite {v | ((cell v).carrier ∩ K).Nonempty}

/--
A tiling graph of `D` before imposing orthogonality. Vertices in the paper are
points of Euclidean space; an injective position map is an equivalent indexed
representation. Cells cover `D` and may extend outside it. Local geometric
arguments use `HasAmbientCollar`, rather than assuming that their exposed faces
are tiled merely from coverage.
-/
structure TilingData (d : ℕ) : Type 1 where
  V : Type
  pos : V → Euc d
  pos_injective : Function.Injective pos
  cell : V → ConvexPolytope d
  domain : Set (Euc d)
  pos_mem_interior : ∀ v, pos v ∈ interior (cell v).carrier
  interiors_pairwise_disjoint : Pairwise fun v w =>
    Disjoint (interior (cell v).carrier) (interior (cell w).carrier)
  cells_cover_domain : domain ⊆ ⋃ v, (cell v).carrier
  locallyFinite : LocallyFiniteCells domain cell

namespace TilingData

variable {d : ℕ} (T : TilingData d)

/-- Every point of the covered set belongs to at least one cell. -/
lemma exists_mem_cell {z : Euc d} (hz : z ∈ T.domain) :
    ∃ v : T.V, z ∈ (T.cell v).carrier :=
  Set.mem_iUnion.mp (T.cells_cover_domain hz)

/-- The graph edge declaration from Section 1.1. -/
def adj (v w : T.V) : Prop :=
  v ≠ w ∧ IsCodimOneFacet (T.cell v).carrier (T.cell w).carrier

lemma adj_irrefl (v : T.V) : ¬ T.adj v v := by
  intro h
  exact h.1 rfl

lemma adj_symm {v w : T.V} (h : T.adj v w) : T.adj w v := by
  exact ⟨Ne.symm h.1, h.2.symm⟩

/-- The common facet associated with an edge. -/
def facet (v w : T.V) : Set (Euc d) :=
  (T.cell v).carrier ∩ (T.cell w).carrier

/-- Euclidean `(d-1)`-volume of a common facet. -/
noncomputable def facetVolume (v w : T.V) : ℝ≥0∞ :=
  μHE[d - 1] (T.facet v w)

/-- Euclidean edge length. -/
noncomputable def edgeLength (v w : T.V) : ℝ≥0∞ :=
  ENNReal.ofReal ‖T.pos w - T.pos v‖

/-- Equation (1.1): canonical conductance. -/
noncomputable def conductance (v w : T.V) : ℝ≥0∞ :=
  T.facetVolume v w / T.edgeLength v w

lemma facet_symm (v w : T.V) : T.facet v w = T.facet w v := by
  simp [facet, Set.inter_comm]

lemma facetVolume_symm (v w : T.V) : T.facetVolume v w = T.facetVolume w v := by
  unfold facetVolume
  rw [T.facet_symm]

lemma edgeLength_symm (v w : T.V) : T.edgeLength v w = T.edgeLength w v := by
  unfold edgeLength
  rw [norm_sub_rev]

lemma conductance_symm (v w : T.V) : T.conductance v w = T.conductance w v := by
  unfold conductance
  rw [T.facetVolume_symm, T.edgeLength_symm]

/-- Orthogonality, expressed without choosing a facet normal. -/
def IsOrthogonal : Prop :=
  ∀ ⦃v w⦄, T.adj v w →
    ∀ ⦃x y⦄, x ∈ T.facet v w → y ∈ T.facet v w →
      inner ℝ (T.pos w - T.pos v) (x - y) = 0

/-- Mesh size `ε_n` in (1.3). -/
noncomputable def mesh : ℝ≥0∞ :=
  ⨆ v : T.V, (T.cell v).diamENN

/-- Infimal tile volume. -/
noncomputable def minTileVolume : ℝ≥0∞ :=
  ⨅ v : T.V, (T.cell v).volume

/-- The quantity inside the maximum in hypothesis (III), written as a supremum. -/
noncomputable def incidentScale (α : ℝ) (v : T.V) : ℝ≥0∞ := by
  classical
  exact ⨆ w : T.V, if T.adj v w then
    (T.edgeLength v w).rpow α * (T.facetVolume v w).rpow α else 0

end TilingData

/-- A genuine orthogonal tiling, not an abstract weighted graph. -/
structure OrthogonalTiling (d : ℕ) : Type 1 extends TilingData d where
  orthogonal : toTilingData.IsOrthogonal

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- The graph adjacency inherited from the underlying tiling. -/
abbrev adj := T.toTilingData.adj

noncomputable abbrev facet := T.toTilingData.facet
noncomputable abbrev facetVolume := T.toTilingData.facetVolume
noncomputable abbrev edgeLength := T.toTilingData.edgeLength
noncomputable abbrev conductance := T.toTilingData.conductance
noncomputable abbrev mesh := T.toTilingData.mesh
noncomputable abbrev minTileVolume := T.toTilingData.minTileVolume
noncomputable abbrev incidentScale := T.toTilingData.incidentScale

end OrthogonalTiling

/-- A sequence of orthogonal tilings of one ambient set `D`. -/
structure TilingSequence (d : ℕ) : Type 1 where
  domain : Set (Euc d)
  tiling : ℕ → OrthogonalTiling d
  common_domain : ∀ n, (tiling n).domain = domain

/-- Hypothesis (I). -/
def RegularityI (d : ℕ) : Prop := d = 2

/--
Literal asymptotic content of hypothesis (II): the lower bound is
`exp(-o(ε_n⁻¹))`. The witness `q_n` is the `o(ε_n⁻¹)` term, expressed as
`ε_n q_n → 0` to avoid dividing by a potentially zero mesh.
-/
def RegularityII {d : ℕ} (G : TilingSequence d) : Prop :=
  ∃ q : ℕ → ℝ,
    Filter.Tendsto
      (fun n => (G.tiling n).mesh.toReal * q n) Filter.atTop (𝓝 0) ∧
    (∀ᶠ n in Filter.atTop,
      0 ≤ q n ∧
      (G.tiling n).minTileVolume.toReal ≥ Real.exp (-q n))

/-- Hypothesis (III), with the uniform eventual big-O constant exposed. -/
def RegularityIII {d : ℕ} (G : TilingSequence d) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ᶠ n in Filter.atTop, ∀ v : (G.tiling n).V,
      ((G.tiling n).cell v).diamENN ≤
        C * (G.tiling n).incidentScale α v

/-- The disjunction of hypotheses (I), (II), and (III) in Theorems A and B. -/
def PaperRegularity {d : ℕ} (G : TilingSequence d) : Prop :=
  RegularityI d ∨ RegularityII G ∨ RegularityIII G

end BouRabeeGwynne

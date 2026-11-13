/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.EndSpatialImage at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.SingularGeometry
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialEnds
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Mathlib.Util.AssertNoSorry

/-!
# Spatial images of graph ends

This file proves **Proposition 2.3** ("Spatial images of ends") of the singular-set manuscript
("An invariance principle for reflected random walks with spatial singularities").

For a face configuration `F` with a singular set (`GeometrySingular`, Definition 1.1) and a graph
end `e` of the cell adjacency graph, the manuscript forms, for each finite vertex set `K`, the
*spherical closure* of the union of the cells indexed by the component of `G \ K` that `e`
selects, and proves that the intersection of these closures over all `K` is a single point of
`Ssing ∪ {∞}`.

Everything happens in the one-point compactification `OnePoint Plane`, which is the manuscript's
Riemann sphere; only its topology is used.

## Deviations from the manuscript's proof, and why

* **The index is the full directed family of finite vertex sets, not a chosen exhaustion.**  The
  manuscript fixes `Kₙ ↑ H` and then argues separately that the resulting point is independent of
  the exhaustion, by cofinality.  Here `K` ranges over all of `Finset V`, directed by `⊆`, and every
  exhaustion is cofinal in that family, so independence of the exhaustion is not a separate
  statement: no exhaustion occurs in `endImage`.  Likewise `endImage` mentions neither the
  geometric witnesses nor any choice of cell representatives, so independence of those is visible
  from the definition rather than proved.
* **The singleton step avoids the chordal metric.**  The manuscript concludes by saying that
  `Ssing ∪ {∞}` is `H¹`-null for the chordal metric of the sphere, while a connected set containing
  two points at distance `r` has `H¹ ≥ r`.  Pinned mathlib puts no metric on `OnePoint X`
  (`Mathlib/Topology/Compactification/OnePoint/Sphere.lean` supplies only homeomorphisms, with no
  measure transfer), so building the chordal metric would be a separate development.  Instead the
  same separation argument is run *in the plane*: if the intersection contained two distinct points
  then, for every `t` in an interval of positive lengths, the open sets `ball z t` and the
  complement of `closedBall z t` (the latter open in `OnePoint Plane` because the closed ball is
  compact) would disconnect each `endCellClosure F e K`, so each of them meets the sphere of radius
  `t`, and hence so does the intersection, by compactness.  The `1`-Lipschitz map `x ↦ dist x z`
  then sends the intersection onto a set containing an interval, forcing `μH[1] > 0` where the
  manuscript's hypothesis `μH[1] Ssing = 0` forces `0`.  This handles the point `∞` uniformly with
  finite points, because `∞` lies outside every `(↑) '' closedBall z t`.
* **Continuity of `e ↦ endImage F e` is stated without an end topology.**  Pinned mathlib defines
  `SimpleGraph.end` (as `Functor.sections`) but puts **no** `TopologicalSpace` instance on it, and
  `Mathlib/Combinatorics/` contains no `TopologicalSpace` instance at all.  Rather than invent one,
  `exists_finset_forall_endImage_mem` states exactly the content the manuscript's continuity proof
  uses: for every neighbourhood `U` of `endImage F e` there is a finite `K` such that *every* end
  agreeing with `e` at `K` has its image in `U`.  In the usual end topology the sets
  `{e' | e'.val (op K) = e.val (op K)}` are a neighbourhood basis at `e`, so this statement is
  continuity for that topology.

## Main results

* `isConnected_biUnion_cell` — a connected graph of connected sets whose members intersect at
  adjacent vertices has connected union.
* `exists_unique_endImage` — Proposition 2.3, equation (2.1).
* `endImage`, `endImageSet_eq_singleton`, `endImage_mem_sing`.
* `exists_forall_endCellClosure_subset` — the uniform localization of (2.1).
* `endImage_eq_infty_iff` — the image is `∞` exactly for the spatial-infinity ends of
  `ReflectedGMS.SpatialEnds.AtSpatialInfinity`.
* `exists_finset_forall_endImage_mem` — continuity, in the topology-free form described above.

## Minimal hypotheses

The argument uses, about the cells, only that every cell is connected and that adjacent cells
intersect (`ConnectedAdjacentCells`), and about the singular set `S` only that `μH[1] S = 0` and
that every point off `S` has a neighbourhood meeting finitely many cells (`LocallyFiniteOff`).
Closedness of `S`, the covering clause, the face rule, the exceptional set `V*`, graph
connectedness and graph local finiteness are never used (the last two only for the anti-vacuity
statement `nonempty_graphEnd_of_infinite`).  The core results are therefore stated under exactly
these hypotheses, with the suffix `_of_cells` (and `endImageSet_subset_of_locallyFiniteOff`,
`endImage_mem_of_locallyFiniteOff`, which need only the local finiteness); the statements from
`GeometrySingular` and `SingularWitness` are recovered from them as thin corollaries under their
original names.  This is what lets the general-cell manuscript's Proposition 2.6, whose witness
has no face rule and no `V*`, reuse the proof verbatim
(`ReflectedGMS/Geometry/EndSpatialImageGeneral.lean`).
-/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology

namespace ReflectedGMS.EndSpatialImage

open SpatialEnds

variable {V : Type*}

/-!
### Chains of adjacent vertices inside a complement component
-/

/-- Walking inside the induced graph on the complement of `K` never leaves the component of the
starting vertex, so it produces a chain of `G`-edges all of whose sources lie in that component. -/
theorem reflTransGen_of_walk {G : SimpleGraph V} {K : Set V} {C : G.ComponentCompl K} :
    ∀ {a b : ↥(Kᶜ : Set V)}, (G.induce (Kᶜ : Set V)).Walk a b → (a : V) ∈ (C : Set V) →
      Relation.ReflTransGen (fun x y : V => G.Adj x y ∧ x ∈ (C : Set V)) (a : V) (b : V) := by
  intro a b p
  induction p with
  | nil => exact fun _ => Relation.ReflTransGen.refl
  | @cons u v w hadj q ih =>
      intro hu
      have hadj' : G.Adj (u : V) (v : V) := hadj
      have hv : (v : V) ∈ (C : Set V) :=
        SimpleGraph.ComponentCompl.mem_of_adj (u : V) (v : V) hu v.2 hadj'
      exact Relation.ReflTransGen.head ⟨hadj', hu⟩ (ih hv)

/-- Any two vertices of a complement component are joined by a chain of graph edges that stays in
the component. -/
theorem reflTransGen_adj_of_mem_componentCompl {G : SimpleGraph V} {K : Set V}
    {C : G.ComponentCompl K} {v v' : V} (hv : v ∈ (C : Set V)) (hv' : v' ∈ (C : Set V)) :
    Relation.ReflTransGen (fun x y : V => G.Adj x y ∧ x ∈ (C : Set V)) v v' := by
  obtain ⟨hvK, hveq⟩ := hv
  obtain ⟨hv'K, hv'eq⟩ := hv'
  have hEq : (G.induce (Kᶜ : Set V)).connectedComponentMk ⟨v, hvK⟩
      = (G.induce (Kᶜ : Set V)).connectedComponentMk ⟨v', hv'K⟩ := hveq.trans hv'eq.symm
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.eq.mp hEq
  exact reflTransGen_of_walk p ⟨hvK, hveq⟩

variable {F : IndexedCells V}

/-!
### The hypotheses the argument uses
-/

/-- The two facts about the cells that the end-image argument uses: every cell is connected, and
adjacent cells intersect.  Both `Geometry` and `GeometrySingular` provide them. -/
structure ConnectedAdjacentCells (F : IndexedCells V) : Prop where
  isConnected : ∀ v, IsConnected (F.cell v : Set Plane)
  adj_inter_nonempty : ∀ ⦃v w⦄, F.graph.toSimpleGraph.Adj v w →
    ((F.cell v : Set Plane) ∩ (F.cell w : Set Plane)).Nonempty

/-- Local finiteness of the cell family off the set `S`: every point outside `S` has a
neighbourhood meeting only finitely many cells.  This is the local-finiteness clause of a singular
witness, for the raw set `S`. -/
def LocallyFiniteOff (F : IndexedCells V) (S : Set Plane) : Prop :=
  ∀ z ∉ S, ∃ U ∈ 𝓝 z, {v | Hits F U v}.Finite

theorem connectedAdjacentCells_of_geometrySingular [Countable V] (h : GeometrySingular F) :
    ConnectedAdjacentCells F :=
  ⟨h.isConnected, h.adj_inter_nonempty⟩

theorem connectedAdjacentCells_of_geometry [Countable V] (h : Geometry F) :
    ConnectedAdjacentCells F :=
  ⟨h.1, h.2.2.2.2.2.2.2⟩

theorem locallyFiniteOff_sing (w : SingularWitness F) : LocallyFiniteOff F w.sing :=
  w.locallyFinite

/-- **A connected graph of connected sets, whose sets intersect at adjacent vertices, has connected
union.**  This is the manuscript's first step in the proof of Proposition 2.3, stated for the cells
indexed by an arbitrary complement component of the cell adjacency graph. -/
theorem isConnected_biUnion_cell_of_cells (hc : ConnectedAdjacentCells F) {K : Set V}
    (C : F.graph.toSimpleGraph.ComponentCompl K) :
    IsConnected (⋃ v ∈ (C : Set V), (F.cell v : Set Plane)) := by
  refine IsConnected.biUnion_of_reflTransGen C.nonempty (fun i _ => hc.isConnected i) ?_
  intro i hi j hj
  exact Relation.ReflTransGen.mono (fun _ _ hxy => ⟨hc.adj_inter_nonempty hxy.1, hxy.2⟩) _ _
    (reflTransGen_adj_of_mem_componentCompl hi hj)

/-- `isConnected_biUnion_cell_of_cells` for a configuration satisfying `GeometrySingular`. -/
theorem isConnected_biUnion_cell [Countable V] (h : GeometrySingular F) {K : Set V}
    (C : F.graph.toSimpleGraph.ComponentCompl K) :
    IsConnected (⋃ v ∈ (C : Set V), (F.cell v : Set Plane)) :=
  isConnected_biUnion_cell_of_cells (connectedAdjacentCells_of_geometrySingular h) C

/-- The vertex set of a configuration with a singular set is nonempty: the cell adjacency graph is
connected, and `SimpleGraph.Connected` carries nonemptiness. -/
theorem nonempty_of_geometrySingular [Countable V] (h : GeometrySingular F) : Nonempty V :=
  h.connected.nonempty

/-!
### The spherical closures
-/

/-- The union of the cells indexed by the component that the end `e` selects outside `K`. -/
def endCellUnion (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) : Set Plane :=
  ⋃ v ∈ endComponent F e K, (F.cell v : Set Plane)

/-- The **spherical closure** of `endCellUnion`, taken in the one-point compactification of the
plane.  Taking the closure there is exactly what adjoins `∞` to an unbounded cell union. -/
def endCellClosure (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) : Set (OnePoint Plane) :=
  closure (((↑) : Plane → OnePoint Plane) '' endCellUnion F e K)

theorem endCellUnion_nonempty (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) :
    (endCellUnion F e K).Nonempty := by
  obtain ⟨v, hv⟩ := (e.val (Opposite.op K)).nonempty
  obtain ⟨x, hx⟩ := (F.cell v).nonempty
  exact ⟨x, mem_biUnion hv hx⟩

theorem endCellClosure_nonempty (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) :
    (endCellClosure F e K).Nonempty := by
  obtain ⟨x, hx⟩ := endCellUnion_nonempty F e K
  exact ⟨((x : OnePoint Plane)), subset_closure ⟨x, hx, rfl⟩⟩

theorem endCellClosure_isClosed (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) :
    IsClosed (endCellClosure F e K) := isClosed_closure

theorem endCellClosure_isCompact (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) :
    IsCompact (endCellClosure F e K) := isClosed_closure.isCompact

theorem isConnected_endCellUnion_of_cells (hc : ConnectedAdjacentCells F) (e : GraphEnd F)
    (K : Finset V) : IsConnected (endCellUnion F e K) :=
  isConnected_biUnion_cell_of_cells hc (e.val (Opposite.op K))

theorem isConnected_endCellUnion [Countable V] (h : GeometrySingular F) (e : GraphEnd F)
    (K : Finset V) : IsConnected (endCellUnion F e K) :=
  isConnected_endCellUnion_of_cells (connectedAdjacentCells_of_geometrySingular h) e K

theorem endCellClosure_isConnected_of_cells (hc : ConnectedAdjacentCells F) (e : GraphEnd F)
    (K : Finset V) : IsConnected (endCellClosure F e K) :=
  ((isConnected_endCellUnion_of_cells hc e K).image _ OnePoint.continuous_coe.continuousOn).closure

theorem endCellClosure_isConnected [Countable V] (h : GeometrySingular F) (e : GraphEnd F)
    (K : Finset V) : IsConnected (endCellClosure F e K) :=
  endCellClosure_isConnected_of_cells (connectedAdjacentCells_of_geometrySingular h) e K

/-!
### Antitonicity in the finite vertex set
-/

theorem endComponent_subset (F : IndexedCells V) (e : GraphEnd F) {K L : Finset V} (hKL : K ⊆ L) :
    endComponent F e L ⊆ endComponent F e K := by
  have hsec : (e.val (Opposite.op L)).hom hKL = e.val (Opposite.op K) :=
    e.prop (CategoryTheory.opHomOfLE (x := Opposite.op K) (y := Opposite.op L) hKL)
  intro v hv
  have hmem := SimpleGraph.ComponentCompl.subset_hom (e.val (Opposite.op L)) hKL hv
  rwa [hsec] at hmem

theorem endCellUnion_subset (F : IndexedCells V) (e : GraphEnd F) {K L : Finset V} (hKL : K ⊆ L) :
    endCellUnion F e L ⊆ endCellUnion F e K := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
  exact mem_biUnion (endComponent_subset F e hKL hv) hxv

theorem endCellClosure_subset (F : IndexedCells V) (e : GraphEnd F) {K L : Finset V}
    (hKL : K ⊆ L) : endCellClosure F e L ⊆ endCellClosure F e K :=
  closure_mono (image_mono (endCellUnion_subset F e hKL))

/-- The family of spherical closures is directed downwards by `⊆` on the index. -/
theorem directed_endCellClosure (F : IndexedCells V) (e : GraphEnd F) :
    Directed (· ⊇ ·) (endCellClosure F e) := by
  classical
  intro K L
  exact ⟨K ∪ L, endCellClosure_subset F e Finset.subset_union_left,
    endCellClosure_subset F e Finset.subset_union_right⟩

/-!
### The intersection
-/

/-- The intersection of the spherical closures over all finite vertex sets: the left-hand side of
the manuscript's equation (2.1). -/
def endImageSet (F : IndexedCells V) (e : GraphEnd F) : Set (OnePoint Plane) :=
  ⋂ K : Finset V, endCellClosure F e K

theorem endImageSet_subset_endCellClosure (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) :
    endImageSet F e ⊆ endCellClosure F e K := iInter_subset _ K

/-- Nested nonempty compact sets have nonempty intersection. -/
theorem endImageSet_nonempty (F : IndexedCells V) (e : GraphEnd F) :
    (endImageSet F e).Nonempty :=
  IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
    (directed_endCellClosure F e) (endCellClosure_nonempty F e)
    (endCellClosure_isCompact F e) (endCellClosure_isClosed F e)

/-- **The intersection avoids every regular point.**  If `z ∉ Ssing` then a neighbourhood of `z`
meets only finitely many cells; those finitely many cells all lie in a finite `K`, so a smaller
neighbourhood of `z` is disjoint from the whole `K`-th cell union, and hence from its closure. -/
theorem endImageSet_subset_of_locallyFiniteOff {S : Set Plane} (hlf : LocallyFiniteOff F S)
    (e : GraphEnd F) :
    endImageSet F e ⊆ (((↑) : Plane → OnePoint Plane) '' S) ∪ {OnePoint.infty} := by
  intro p hp
  cases p with
  | infty => exact Or.inr rfl
  | coe z =>
      refine Or.inl ⟨z, ?_, rfl⟩
      by_contra hz
      obtain ⟨U, hU, hfin⟩ := hlf z hz
      obtain ⟨U', hU'U, hU'open, hzU'⟩ := _root_.mem_nhds_iff.mp hU
      have hdisj : ((↑) : Plane → OnePoint Plane) '' endCellUnion F e hfin.toFinset
          ⊆ ((((↑) : Plane → OnePoint Plane) '' U')ᶜ) := by
        intro a ha hmem
        obtain ⟨x, hx, rfl⟩ := ha
        obtain ⟨y, hyU', hxy⟩ := hmem
        have hyx : y = x := OnePoint.coe_injective hxy
        obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
        have hvK : v ∉ hfin.toFinset := by
          have hnot := SimpleGraph.ComponentCompl.notMem_of_mem hv
          simpa using hnot
        exact hvK (hfin.mem_toFinset.mpr ⟨x, hxv, hU'U (hyx ▸ hyU')⟩)
      have hclosed : IsClosed ((((↑) : Plane → OnePoint Plane) '' U')ᶜ) :=
        (OnePoint.isOpen_image_coe.2 hU'open).isClosed_compl
      have hsub : endCellClosure F e hfin.toFinset ⊆ ((((↑) : Plane → OnePoint Plane) '' U')ᶜ) :=
        closure_minimal hdisj hclosed
      exact hsub (endImageSet_subset_endCellClosure F e _ hp) ⟨z, hzU', rfl⟩

/-- `endImageSet_subset_of_locallyFiniteOff` for the singular set of a `SingularWitness`. -/
theorem endImageSet_subset_sing (w : SingularWitness F) (e : GraphEnd F) :
    endImageSet F e ⊆ (((↑) : Plane → OnePoint Plane) '' w.sing) ∪ {OnePoint.infty} :=
  endImageSet_subset_of_locallyFiniteOff (locallyFiniteOff_sing w) e

/-!
### The one-dimensional Hausdorff lower bound
-/

/-- A set meeting the sphere of radius `t` about `z` for every `t ∈ (0, ρ)` has one-dimensional
Hausdorff measure at least `ρ`.

This is the manuscript's "a connected subset containing points at distance `r > 0` has `H¹ ≥ r`",
in the form in which it is used here: `x ↦ dist x z` is `1`-Lipschitz, hence cannot increase `H¹`,
while its image contains an interval, whose `H¹` is its length because `μH[1] = volume` on `ℝ`.
Pinned mathlib has no lemma bounding `μH[1]` of a connected set below by its diameter; this was
searched for both as a diameter bound and as a statement combining `IsPreconnected` with `μH`, and
neither exists. -/
theorem ofReal_le_hausdorffMeasure_of_forall_dist {S : Set Plane} {z : Plane} {ρ : ℝ}
    (hS : ∀ t ∈ Ioo (0 : ℝ) ρ, ∃ x ∈ S, dist x z = t) :
    ENNReal.ofReal ρ ≤ μH[(1 : ℝ)] S := by
  have himg : Ioo (0 : ℝ) ρ ⊆ (fun x : Plane => dist x z) '' S := by
    intro t ht
    obtain ⟨x, hx, hxt⟩ := hS t ht
    exact ⟨x, hx, hxt⟩
  have hlip : LipschitzWith 1 (fun x : Plane => dist x z) := LipschitzWith.dist_left z
  have h1 : μH[(1 : ℝ)] ((fun x : Plane => dist x z) '' S) ≤ μH[(1 : ℝ)] S := by
    simpa using hlip.hausdorffMeasure_image_le (d := (1 : ℝ)) zero_le_one S
  have hvol : μH[(1 : ℝ)] (Ioo (0 : ℝ) ρ) = ENNReal.ofReal ρ := by
    rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Ioo, sub_zero]
  have h2 := MeasureTheory.measure_mono (μ := (μH[(1 : ℝ)] : MeasureTheory.Measure ℝ)) himg
  rw [hvol] at h2
  exact h2.trans h1

/-!
### The intersection is a single point
-/

/-- If the intersection contains a finite point `z` and any other point `q` lying outside
`(↑) '' closedBall z t`, then it meets the sphere of radius `t` about `z`.

Each `endCellClosure F e K` is connected and meets both `(↑) '' ball z t` (at `z`) and the open set
`((↑) '' closedBall z t)ᶜ` (at `q`), which are disjoint; so it must meet the sphere.  Those
intersections form a directed family of nonempty compact sets, so the intersection does too. -/
theorem endImageSet_meets_sphere_of_cells (hc : ConnectedAdjacentCells F) (e : GraphEnd F)
    {z : Plane} (hz : ((z : OnePoint Plane)) ∈ endImageSet F e)
    {q : OnePoint Plane} (hq : q ∈ endImageSet F e) {t : ℝ} (ht : 0 < t)
    (hqt : q ∉ ((↑) : Plane → OnePoint Plane) '' closedBall z t) :
    ∃ x ∈ sphere z t, ((x : OnePoint Plane)) ∈ endImageSet F e := by
  classical
  set A : Set (OnePoint Plane) := ((↑) : Plane → OnePoint Plane) '' sphere z t with hA
  have hAcompact : IsCompact A := (isCompact_sphere z t).image OnePoint.continuous_coe
  have hAclosed : IsClosed A := hAcompact.isClosed
  have hstep : ∀ K : Finset V, (endCellClosure F e K ∩ A).Nonempty := by
    intro K
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hUopen : IsOpen (((↑) : Plane → OnePoint Plane) '' ball z t) :=
      OnePoint.isOpen_image_coe.2 Metric.isOpen_ball
    have hWopen : IsOpen ((((↑) : Plane → OnePoint Plane) '' closedBall z t)ᶜ) :=
      OnePoint.isOpen_compl_image_coe.2 ⟨Metric.isClosed_closedBall, isCompact_closedBall z t⟩
    have hzC : ((z : OnePoint Plane)) ∈ endCellClosure F e K :=
      endImageSet_subset_endCellClosure F e K hz
    have hqC : q ∈ endCellClosure F e K := endImageSet_subset_endCellClosure F e K hq
    have hzU : ((z : OnePoint Plane)) ∈ ((↑) : Plane → OnePoint Plane) '' ball z t :=
      ⟨z, Metric.mem_ball_self ht, rfl⟩
    have hcover : endCellClosure F e K ⊆
        (((↑) : Plane → OnePoint Plane) '' ball z t) ∪
          ((((↑) : Plane → OnePoint Plane) '' closedBall z t)ᶜ) := by
      intro y hy
      by_cases hyW : y ∈ ((((↑) : Plane → OnePoint Plane) '' closedBall z t)ᶜ)
      · exact Or.inr hyW
      · refine Or.inl ?_
        rw [Set.notMem_compl_iff] at hyW
        obtain ⟨x, hxb, rfl⟩ := hyW
        by_cases hxball : x ∈ ball z t
        · exact ⟨x, hxball, rfl⟩
        · exfalso
          have hxs : x ∈ sphere z t :=
            Metric.mem_sphere.mpr
              (le_antisymm (Metric.mem_closedBall.mp hxb)
                (not_lt.mp fun hlt => hxball (Metric.mem_ball.mpr hlt)))
          have hmem2 : ((x : OnePoint Plane)) ∈ endCellClosure F e K ∩ A := ⟨hy, ⟨x, hxs, rfl⟩⟩
          rw [hcon] at hmem2
          exact hmem2
    obtain ⟨y, _, hy2⟩ :=
      (endCellClosure_isConnected_of_cells hc e K).isPreconnected _ _ hUopen hWopen
      hcover ⟨_, hzC, hzU⟩ ⟨q, hqC, hqt⟩
    exact hy2.2 (image_mono Metric.ball_subset_closedBall hy2.1)
  have hdir : Directed (· ⊇ ·) (fun K : Finset V => endCellClosure F e K ∩ A) := by
    intro K L
    exact ⟨K ∪ L,
      inter_subset_inter_left A (endCellClosure_subset F e Finset.subset_union_left),
      inter_subset_inter_left A (endCellClosure_subset F e Finset.subset_union_right)⟩
  have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ hdir hstep
    (fun K => (endCellClosure_isCompact F e K).inter_right hAclosed)
    (fun K => (endCellClosure_isClosed F e K).inter hAclosed)
  rw [← Set.iInter_inter] at hne
  obtain ⟨p, hp1, hp2⟩ := hne
  obtain ⟨x, hx, rfl⟩ := hp2
  exact ⟨x, hx, hp1⟩

/-- `endImageSet_meets_sphere_of_cells` for a configuration satisfying `GeometrySingular`. -/
theorem endImageSet_meets_sphere [Countable V] (h : GeometrySingular F) (e : GraphEnd F)
    {z : Plane} (hz : ((z : OnePoint Plane)) ∈ endImageSet F e)
    {q : OnePoint Plane} (hq : q ∈ endImageSet F e) {t : ℝ} (ht : 0 < t)
    (hqt : q ∉ ((↑) : Plane → OnePoint Plane) '' closedBall z t) :
    ∃ x ∈ sphere z t, ((x : OnePoint Plane)) ∈ endImageSet F e :=
  endImageSet_meets_sphere_of_cells (connectedAdjacentCells_of_geometrySingular h) e hz hq ht hqt

/-- **The intersection has at most one point.** -/
theorem endImageSet_subsingleton_of_cells (hc : ConnectedAdjacentCells F) {S : Set Plane}
    (hS : μH[(1 : ℝ)] S = 0) (hlf : LocallyFiniteOff F S) (e : GraphEnd F) :
    (endImageSet F e).Subsingleton := by
  have key : ∀ z : Plane, ((z : OnePoint Plane)) ∈ endImageSet F e →
      ∀ q : OnePoint Plane, q ∈ endImageSet F e → ∀ ρ : ℝ, 0 < ρ →
      (∀ t ∈ Ioo (0 : ℝ) ρ, q ∉ ((↑) : Plane → OnePoint Plane) '' closedBall z t) → False := by
    intro z hz q hq ρ hρ hout
    have hsph : ∀ t ∈ Ioo (0 : ℝ) ρ,
        ∃ x ∈ {y : Plane | ((y : OnePoint Plane)) ∈ endImageSet F e}, dist x z = t := by
      intro t ht
      obtain ⟨x, hxs, hxmem⟩ := endImageSet_meets_sphere_of_cells hc e hz hq ht.1 (hout t ht)
      exact ⟨x, hxmem, Metric.mem_sphere.mp hxs⟩
    have hle := ofReal_le_hausdorffMeasure_of_forall_dist hsph
    have hsub : {y : Plane | ((y : OnePoint Plane)) ∈ endImageSet F e} ⊆ S := by
      intro y hy
      rcases endImageSet_subset_of_locallyFiniteOff hlf e hy with hy1 | hy1
      · obtain ⟨u, hu, huy⟩ := hy1
        obtain rfl : u = y := OnePoint.coe_injective huy
        exact hu
      · exact absurd (hy1 : ((y : OnePoint Plane)) = OnePoint.infty) (OnePoint.coe_ne_infty y)
    have hzero : μH[(1 : ℝ)] {y : Plane | ((y : OnePoint Plane)) ∈ endImageSet F e} = 0 :=
      MeasureTheory.measure_mono_null hsub hS
    rw [hzero] at hle
    exact absurd hle (not_le.mpr (ENNReal.ofReal_pos.mpr hρ))
  intro p hp q hq
  by_contra hpq
  cases p with
  | infty =>
      cases q with
      | infty => exact hpq rfl
      | coe y =>
          refine key y hq OnePoint.infty hp 1 one_pos ?_
          intro t _ hmem
          exact OnePoint.infty_notMem_image_coe hmem
  | coe x =>
      cases q with
      | infty =>
          refine key x hp OnePoint.infty hq 1 one_pos ?_
          intro t _ hmem
          exact OnePoint.infty_notMem_image_coe hmem
      | coe y =>
          have hxy : x ≠ y := fun hxy => hpq (by rw [hxy])
          refine key x hp ((y : OnePoint Plane)) hq (dist y x) (dist_pos.mpr (Ne.symm hxy)) ?_
          intro t ht hmem
          obtain ⟨u, hu, huy⟩ := hmem
          obtain rfl : u = y := OnePoint.coe_injective huy
          exact absurd (Metric.mem_closedBall.mp hu) (not_le.mpr ht.2)

/-- `endImageSet_subsingleton_of_cells` for a configuration satisfying `GeometrySingular`, with the
singular set of a `SingularWitness`. -/
theorem endImageSet_subsingleton [Countable V] (h : GeometrySingular F) (w : SingularWitness F)
    (e : GraphEnd F) : (endImageSet F e).Subsingleton :=
  endImageSet_subsingleton_of_cells (connectedAdjacentCells_of_geometrySingular h)
    w.hausdorff_sing (locallyFiniteOff_sing w) e

/-- **Proposition 2.3, equation (2.1)**, under the minimal hypotheses.  The intersection over all
finite vertex sets of the spherical closures of the cell unions of the components selected by the
end `e` is a single point, and that point lies in `S ∪ {∞}`. -/
theorem exists_unique_endImage_of_cells (hc : ConnectedAdjacentCells F) {S : Set Plane}
    (hS : μH[(1 : ℝ)] S = 0) (hlf : LocallyFiniteOff F S) (e : GraphEnd F) :
    ∃ p : OnePoint Plane, (⋂ K : Finset V, endCellClosure F e K) = {p} ∧
      (p = OnePoint.infty ∨ ∃ z ∈ S, p = ((z : OnePoint Plane))) := by
  obtain ⟨p, hp⟩ := endImageSet_nonempty F e
  refine ⟨p, (endImageSet_subsingleton_of_cells hc hS hlf e).eq_singleton_of_mem hp, ?_⟩
  rcases endImageSet_subset_of_locallyFiniteOff hlf e hp with h1 | h1
  · obtain ⟨z, hz, hzp⟩ := h1
    exact Or.inr ⟨z, hz, hzp.symm⟩
  · exact Or.inl h1

/-- **Proposition 2.3, equation (2.1).**  The intersection over all finite vertex sets of the
spherical closures of the cell unions of the components selected by the end `e` is a single point,
and that point lies in `Ssing ∪ {∞}`. -/
theorem exists_unique_endImage [Countable V] (h : GeometrySingular F) (w : SingularWitness F)
    (e : GraphEnd F) :
    ∃ p : OnePoint Plane, (⋂ K : Finset V, endCellClosure F e K) = {p} ∧
      (p = OnePoint.infty ∨ ∃ z ∈ w.sing, p = ((z : OnePoint Plane))) :=
  exists_unique_endImage_of_cells (connectedAdjacentCells_of_geometrySingular h) w.hausdorff_sing
    (locallyFiniteOff_sing w) e

/-!
### The spatial image as a function
-/

/-- The **spatial image of a graph end**.

It depends only on the cell configuration and the end: no exhaustion, no geometric witness and no
choice of cell representatives occurs in its definition, which is why the manuscript's assertions
that `p_ω` is independent of all three need no separate proof here. -/
noncomputable def endImage (F : IndexedCells V) (e : GraphEnd F) : OnePoint Plane :=
  Classical.choose (endImageSet_nonempty F e)

theorem endImage_mem (F : IndexedCells V) (e : GraphEnd F) : endImage F e ∈ endImageSet F e :=
  Classical.choose_spec (endImageSet_nonempty F e)

theorem endImageSet_eq_singleton_of_cells (hc : ConnectedAdjacentCells F) {S : Set Plane}
    (hS : μH[(1 : ℝ)] S = 0) (hlf : LocallyFiniteOff F S) (e : GraphEnd F) :
    endImageSet F e = {endImage F e} :=
  (endImageSet_subsingleton_of_cells hc hS hlf e).eq_singleton_of_mem (endImage_mem F e)

theorem endImageSet_eq_singleton [Countable V] (h : GeometrySingular F) (w : SingularWitness F)
    (e : GraphEnd F) : endImageSet F e = {endImage F e} :=
  endImageSet_eq_singleton_of_cells (connectedAdjacentCells_of_geometrySingular h)
    w.hausdorff_sing (locallyFiniteOff_sing w) e

/-- The spatial image lies in `S ∪ {∞}` for every set `S` off which the cells are locally
finite. -/
theorem endImage_mem_of_locallyFiniteOff {S : Set Plane} (hlf : LocallyFiniteOff F S)
    (e : GraphEnd F) :
    endImage F e = OnePoint.infty ∨ ∃ z ∈ S, endImage F e = ((z : OnePoint Plane)) := by
  rcases endImageSet_subset_of_locallyFiniteOff hlf e (endImage_mem F e) with h1 | h1
  · obtain ⟨z, hz, hzp⟩ := h1
    exact Or.inr ⟨z, hz, hzp.symm⟩
  · exact Or.inl h1

/-- The spatial image lies in `Ssing ∪ {∞}`. -/
theorem endImage_mem_sing (w : SingularWitness F) (e : GraphEnd F) :
    endImage F e = OnePoint.infty ∨ ∃ z ∈ w.sing, endImage F e = ((z : OnePoint Plane)) :=
  endImage_mem_of_locallyFiniteOff (locallyFiniteOff_sing w) e

/-!
### Uniform localization
-/

/-- **Uniform localization.**  For every spherical neighbourhood `U` of the spatial image, the cell
union of (2.1) is contained in `U` for all sufficiently large finite vertex sets.

If no `endCellClosure F e K` were contained in `U`, the nested compact sets `endCellClosure F e K \ U`
would have nonempty intersection, contradicting the fact that the intersection is `{endImage F e}`,
which lies in `U`. -/
theorem exists_forall_endCellClosure_subset_of_cells (hc : ConnectedAdjacentCells F)
    {S : Set Plane} (hS : μH[(1 : ℝ)] S = 0) (hlf : LocallyFiniteOff F S) (e : GraphEnd F)
    {U : Set (OnePoint Plane)} (hU : IsOpen U) (hmem : endImage F e ∈ U) :
    ∃ K₀ : Finset V, ∀ K : Finset V, K₀ ⊆ K → endCellClosure F e K ⊆ U := by
  classical
  by_cases hex : ∃ K₀ : Finset V, endCellClosure F e K₀ ⊆ U
  · obtain ⟨K₀, hK₀⟩ := hex
    exact ⟨K₀, fun K hK => (endCellClosure_subset F e hK).trans hK₀⟩
  · exfalso
    have hex' := not_exists.mp hex
    have hstep : ∀ K : Finset V, (endCellClosure F e K ∩ Uᶜ).Nonempty := by
      intro K
      obtain ⟨y, hy1, hy2⟩ := Set.not_subset.mp (hex' K)
      exact ⟨y, hy1, hy2⟩
    have hdir : Directed (· ⊇ ·) (fun K : Finset V => endCellClosure F e K ∩ Uᶜ) := by
      intro K L
      exact ⟨K ∪ L,
        inter_subset_inter_left _ (endCellClosure_subset F e Finset.subset_union_left),
        inter_subset_inter_left _ (endCellClosure_subset F e Finset.subset_union_right)⟩
    have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ hdir hstep
      (fun K => (endCellClosure_isCompact F e K).inter_right hU.isClosed_compl)
      (fun K => (endCellClosure_isClosed F e K).inter hU.isClosed_compl)
    rw [← Set.iInter_inter] at hne
    obtain ⟨p, hp1, hp2⟩ := hne
    have hp1' : p ∈ endImageSet F e := hp1
    rw [endImageSet_eq_singleton_of_cells hc hS hlf e, Set.mem_singleton_iff] at hp1'
    exact hp2 (by rw [hp1']; exact hmem)

theorem exists_forall_endCellClosure_subset [Countable V] (h : GeometrySingular F)
    (w : SingularWitness F) (e : GraphEnd F) {U : Set (OnePoint Plane)} (hU : IsOpen U)
    (hmem : endImage F e ∈ U) :
    ∃ K₀ : Finset V, ∀ K : Finset V, K₀ ⊆ K → endCellClosure F e K ⊆ U :=
  exists_forall_endCellClosure_subset_of_cells (connectedAdjacentCells_of_geometrySingular h)
    w.hausdorff_sing (locallyFiniteOff_sing w) e hU hmem

/-!
### The image is `∞` exactly at the spatial-infinity ends
-/

/-- **The spatial image is `∞` precisely for the spatial-infinity ends.**  `AtSpatialInfinity` is
taken verbatim from `ReflectedGMS.SpatialEnds`. -/
theorem endImage_eq_infty_iff_of_cells (hc : ConnectedAdjacentCells F) {S : Set Plane}
    (hS : μH[(1 : ℝ)] S = 0) (hlf : LocallyFiniteOff F S) (e : GraphEnd F) :
    endImage F e = OnePoint.infty ↔ AtSpatialInfinity F e := by
  constructor
  · intro hinf R
    have hU : IsOpen ((((↑) : Plane → OnePoint Plane) '' closedBall (0 : Plane) R)ᶜ) :=
      OnePoint.isOpen_compl_image_coe.2 ⟨Metric.isClosed_closedBall, isCompact_closedBall _ _⟩
    have hmemU : endImage F e ∈ ((((↑) : Plane → OnePoint Plane) '' closedBall (0 : Plane) R)ᶜ) := by
      rw [hinf]
      exact OnePoint.infty_notMem_image_coe
    obtain ⟨K₀, hK₀⟩ := exists_forall_endCellClosure_subset_of_cells hc hS hlf e hU hmemU
    refine ⟨K₀, fun L hL v hv y hy => ?_⟩
    have hyU : ((y : OnePoint Plane)) ∈
        ((((↑) : Plane → OnePoint Plane) '' closedBall (0 : Plane) R)ᶜ) :=
      hK₀ L hL (subset_closure ⟨y, mem_biUnion hv hy, rfl⟩)
    have hyb : y ∉ closedBall (0 : Plane) R := fun hyb => hyU ⟨y, hyb, rfl⟩
    have hd : ¬ dist y (0 : Plane) ≤ R := fun hdd => hyb (Metric.mem_closedBall.mpr hdd)
    rw [dist_zero_right] at hd
    exact not_le.mp hd
  · intro hinfty
    by_contra hne
    obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hne
    obtain ⟨K, hK⟩ := hinfty (‖z‖ + 1)
    have hsub : endCellUnion F e K ⊆ (ball (0 : Plane) (‖z‖ + 1))ᶜ := by
      intro y hy hyb
      obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
      have hlt := hK K (subset_refl K) v hv y hyv
      rw [Metric.mem_ball, dist_zero_right] at hyb
      exact absurd hyb (not_lt.mpr (le_of_lt hlt))
    have hclosed : IsClosed ((((↑) : Plane → OnePoint Plane) '' ball (0 : Plane) (‖z‖ + 1))ᶜ) :=
      (OnePoint.isOpen_image_coe.2 Metric.isOpen_ball).isClosed_compl
    have himg : ((↑) : Plane → OnePoint Plane) '' endCellUnion F e K ⊆
        ((((↑) : Plane → OnePoint Plane) '' ball (0 : Plane) (‖z‖ + 1))ᶜ) := by
      intro a ha hmem
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨u, hu, hue⟩ := hmem
      obtain rfl : u = y := OnePoint.coe_injective hue
      exact hsub hy hu
    have hcc : endCellClosure F e K ⊆
        ((((↑) : Plane → OnePoint Plane) '' ball (0 : Plane) (‖z‖ + 1))ᶜ) :=
      closure_minimal himg hclosed
    have hmem : endImage F e ∈ endCellClosure F e K :=
      endImageSet_subset_endCellClosure F e K (endImage_mem F e)
    rw [← hz] at hmem
    exact hcc hmem ⟨z, by rw [Metric.mem_ball, dist_zero_right]; exact lt_add_one _, rfl⟩

theorem endImage_eq_infty_iff [Countable V] (h : GeometrySingular F) (w : SingularWitness F)
    (e : GraphEnd F) : endImage F e = OnePoint.infty ↔ AtSpatialInfinity F e :=
  endImage_eq_infty_iff_of_cells (connectedAdjacentCells_of_geometrySingular h) w.hausdorff_sing
    (locallyFiniteOff_sing w) e

/-!
### Continuity
-/

theorem endCellClosure_congr (F : IndexedCells V) {e e' : GraphEnd F} (K : Finset V)
    (hK : e.val (Opposite.op K) = e'.val (Opposite.op K)) :
    endCellClosure F e K = endCellClosure F e' K := by
  have h1 : endComponent F e K = endComponent F e' K := by
    show (e.val (Opposite.op K)).supp = (e'.val (Opposite.op K)).supp
    rw [hK]
  unfold endCellClosure endCellUnion
  rw [h1]

/-- **Continuity of the spatial image**, in the form the manuscript's proof gives it and without
assuming an end topology (pinned mathlib puts none on `SimpleGraph.end`): every end that agrees with
`e` at a suitable finite vertex set has its spatial image in the prescribed neighbourhood.  The sets
`{e' | e'.val (op K) = e.val (op K)}` are a neighbourhood basis of `e` in the usual end topology, so
this is continuity for that topology. -/
theorem exists_finset_forall_endImage_mem_of_cells (hc : ConnectedAdjacentCells F)
    {S : Set Plane} (hS : μH[(1 : ℝ)] S = 0) (hlf : LocallyFiniteOff F S) (e : GraphEnd F)
    {U : Set (OnePoint Plane)} (hU : IsOpen U) (hmem : endImage F e ∈ U) :
    ∃ K : Finset V, ∀ e' : GraphEnd F,
      e'.val (Opposite.op K) = e.val (Opposite.op K) → endImage F e' ∈ U := by
  obtain ⟨K₀, hK₀⟩ := exists_forall_endCellClosure_subset_of_cells hc hS hlf e hU hmem
  refine ⟨K₀, fun e' he' => ?_⟩
  have h1 : endCellClosure F e' K₀ = endCellClosure F e K₀ := endCellClosure_congr F K₀ he'
  have h2 : endImage F e' ∈ endCellClosure F e' K₀ :=
    endImageSet_subset_endCellClosure F e' K₀ (endImage_mem F e')
  rw [h1] at h2
  exact hK₀ K₀ (subset_refl K₀) h2

theorem exists_finset_forall_endImage_mem [Countable V] (h : GeometrySingular F)
    (w : SingularWitness F) (e : GraphEnd F) {U : Set (OnePoint Plane)} (hU : IsOpen U)
    (hmem : endImage F e ∈ U) :
    ∃ K : Finset V, ∀ e' : GraphEnd F,
      e'.val (Opposite.op K) = e.val (Opposite.op K) → endImage F e' ∈ U :=
  exists_finset_forall_endImage_mem_of_cells (connectedAdjacentCells_of_geometrySingular h)
    w.hausdorff_sing (locallyFiniteOff_sing w) e hU hmem

/-!
### A consistency check on (2.1)

The conclusion of `exists_unique_endImage` is not a formality: it pins the point down.  When the
cells cover the whole plane, i.e. the singular set is empty, it forces the spatial image of *every*
end to be `∞`, which is the expected specialisation (local finiteness everywhere makes a component
that stayed in a bounded region finite).
-/

/-- **Anti-vacuity.**  A configuration with a singular set whose vertex set is infinite has at
least one end, so `exists_unique_endImage` is not a statement about an empty index: the cell
adjacency graph is connected and locally finite by `GeometrySingular`, and mathlib's
`SimpleGraph.nonempty_ends_of_infinite` then applies.  (The type variable is at `Type` because that
is the universe of the mathlib lemma.) -/
theorem nonempty_graphEnd_of_infinite {W : Type} [Countable W] [Infinite W] {F' : IndexedCells W}
    (h : GeometrySingular F') : (GraphEnd F').Nonempty := by
  haveI : Fact F'.graph.toSimpleGraph.Preconnected := ⟨h.connected.preconnected⟩
  haveI : F'.graph.toSimpleGraph.LocallyFinite := fun v => (h.neighborSet_finite v).fintype
  exact SimpleGraph.nonempty_ends_of_infinite _

/-- With an empty singular set every end has spatial image `∞`. -/
theorem endImage_eq_infty_of_sing_eq_empty (w : SingularWitness F) (hsing : w.sing = ∅)
    (e : GraphEnd F) : endImage F e = OnePoint.infty := by
  rcases endImage_mem_sing w e with h1 | ⟨z, hz, -⟩
  · exact h1
  · rw [hsing] at hz
    exact hz.elim

end ReflectedGMS.EndSpatialImage

assert_no_sorry ReflectedGMS.EndSpatialImage.isConnected_biUnion_cell
assert_no_sorry ReflectedGMS.EndSpatialImage.endCellClosure_isConnected
assert_no_sorry ReflectedGMS.EndSpatialImage.exists_unique_endImage
assert_no_sorry ReflectedGMS.EndSpatialImage.endImageSet_eq_singleton
assert_no_sorry ReflectedGMS.EndSpatialImage.endImage_mem_sing
assert_no_sorry ReflectedGMS.EndSpatialImage.exists_forall_endCellClosure_subset
assert_no_sorry ReflectedGMS.EndSpatialImage.endImage_eq_infty_iff
assert_no_sorry ReflectedGMS.EndSpatialImage.exists_finset_forall_endImage_mem
assert_no_sorry ReflectedGMS.EndSpatialImage.ofReal_le_hausdorffMeasure_of_forall_dist
assert_no_sorry ReflectedGMS.EndSpatialImage.endImage_eq_infty_of_sing_eq_empty
assert_no_sorry ReflectedGMS.EndSpatialImage.nonempty_graphEnd_of_infinite
assert_no_sorry ReflectedGMS.EndSpatialImage.exists_unique_endImage_of_cells
assert_no_sorry ReflectedGMS.EndSpatialImage.endImageSet_eq_singleton_of_cells
assert_no_sorry ReflectedGMS.EndSpatialImage.endImage_mem_of_locallyFiniteOff
assert_no_sorry ReflectedGMS.EndSpatialImage.endImage_eq_infty_iff_of_cells
assert_no_sorry ReflectedGMS.EndSpatialImage.exists_finset_forall_endImage_mem_of_cells

#print axioms ReflectedGMS.EndSpatialImage.isConnected_biUnion_cell
#print axioms ReflectedGMS.EndSpatialImage.endCellClosure_isConnected
#print axioms ReflectedGMS.EndSpatialImage.exists_unique_endImage
#print axioms ReflectedGMS.EndSpatialImage.endImageSet_eq_singleton
#print axioms ReflectedGMS.EndSpatialImage.endImage_mem_sing
#print axioms ReflectedGMS.EndSpatialImage.exists_forall_endCellClosure_subset
#print axioms ReflectedGMS.EndSpatialImage.endImage_eq_infty_iff
#print axioms ReflectedGMS.EndSpatialImage.exists_finset_forall_endImage_mem
#print axioms ReflectedGMS.EndSpatialImage.ofReal_le_hausdorffMeasure_of_forall_dist
#print axioms ReflectedGMS.EndSpatialImage.endImage_eq_infty_of_sing_eq_empty
#print axioms ReflectedGMS.EndSpatialImage.nonempty_graphEnd_of_infinite
#print axioms ReflectedGMS.EndSpatialImage.exists_unique_endImage_of_cells
#print axioms ReflectedGMS.EndSpatialImage.endImageSet_eq_singleton_of_cells
#print axioms ReflectedGMS.EndSpatialImage.endImage_mem_of_locallyFiniteOff
#print axioms ReflectedGMS.EndSpatialImage.endImage_eq_infty_iff_of_cells
#print axioms ReflectedGMS.EndSpatialImage.exists_finset_forall_endImage_mem_of_cells

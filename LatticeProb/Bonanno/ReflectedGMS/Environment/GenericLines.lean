/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.GenericLines at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.SingularGeometry
import LatticeProb.Bonanno.ReflectedGMS.Environment.AELineConnectivity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Generic lines and finite boundaries

This file proves **Proposition 2.1** of the singular-set manuscript: under Definition 1.1
(`ReflectedGMS.GeometrySingular`) there are Lebesgue-null exceptional sets `Nh, Nv ⊆ ℝ` such that
for every offset outside them, *every* nondegenerate closed segment at that offset is met by only
finitely many cells and the induced subgraph on those cells is connected.

The two null sets are produced **once and for all**, so that the conclusion holds simultaneously for
every pair of segment endpoints; this is exactly the quantifier order that
`ReflectedGMS.AELineConnected` and the whole AE-LC corpus use.

The main consequences are:

* `ReflectedGMS.exists_null_sets_segment_finite_and_reachable` — Proposition 2.1 with explicit null
  sets, carrying both the finiteness and the connectivity half (the finiteness half is what
  Corollary 2.2 on good spatial rectangles consumes);
* `ReflectedGMS.aeLineConnected_of_geometrySingular` — the derived `AELineConnected F`, which is the
  hypothesis that `ReflectedGMS.Code.Valid` takes as an input.

The mathematical content is isolated in
`ReflectedGMS.finite_and_segmentReachable_of_isCompact_of_isPreconnected`, which is the honest
general statement: *any* compact preconnected subset of the plane avoiding `Ssing ∪ V*` meets
finitely many cells and induces a connected subgraph.  The horizontal and vertical halves of
Proposition 2.1 are two instances of it, and Corollary 2.2 will use the same lemma for the four
sides of a rectangle.

Proof of the general lemma, following the manuscript:

* the coordinate projections are `1`-Lipschitz, so `H¹(pᵢ(Ssing)) ≤ H¹(Ssing) = 0`, and on `ℝ`
  one-dimensional Hausdorff measure is Lebesgue measure; the projection of the countable set `V*` is
  countable, hence null as well;
* a segment at a good offset avoids `Ssing ∪ V*` entirely, so each of its points has a neighbourhood
  meeting finitely many cells, and compactness turns this into global finiteness;
* if the induced graph were disconnected, the reachability class of one vertex and its complement
  would split the segment into two nonempty disjoint relatively closed pieces — disjoint precisely
  because a shared point would lie outside `Ssing ∪ V*` in two distinct cells and hence force
  adjacency by Definition 1.1(iv).  That contradicts connectedness of a closed interval.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace ReflectedGMS

variable {V : Type*}

/-! ### Coordinate projections are `1`-Lipschitz -/

/-- The `i`-th coordinate projection of the plane; `coordProj 0` is `p_x` and `coordProj 1` is
`p_y` in the notation of the manuscript. -/
def coordProj (i : Fin 2) : Plane → ℝ := fun z => z i

@[simp] theorem coordProj_apply (i : Fin 2) (z : Plane) : coordProj i z = z i := rfl

theorem lipschitzWith_coordProj (i : Fin 2) : LipschitzWith 1 (coordProj i) :=
  LipschitzWith.mk_one fun z w => PiLp.dist_apply_le z w i

/-- Projecting an `H¹`-null subset of the plane to a coordinate axis gives a Lebesgue-null subset of
`ℝ`: the projection is `1`-Lipschitz, and on `ℝ` one-dimensional Hausdorff measure is Lebesgue
measure. -/
theorem volume_image_coordProj_eq_zero (i : Fin 2) {S : Set Plane} (hS : μH[1] S = 0) :
    volume (coordProj i '' S) = 0 := by
  have h := (lipschitzWith_coordProj i).hausdorffMeasure_image_le (d := 1) zero_le_one S
  rw [hS, mul_zero] at h
  rw [← hausdorffMeasure_real]
  exact le_antisymm h (by simp)

/-! ### Segments are compact and connected -/

/-- The point `(t, y)` of the plane. -/
noncomputable def horizontalPoint (y t : ℝ) : Plane := WithLp.toLp 2 ![t, y]

/-- The point `(x, t)` of the plane. -/
noncomputable def verticalPoint (x t : ℝ) : Plane := WithLp.toLp 2 ![x, t]

@[simp] theorem horizontalPoint_apply_zero (y t : ℝ) : horizontalPoint y t 0 = t := by
  simp [horizontalPoint]

@[simp] theorem horizontalPoint_apply_one (y t : ℝ) : horizontalPoint y t 1 = y := by
  simp [horizontalPoint]

@[simp] theorem verticalPoint_apply_zero (x t : ℝ) : verticalPoint x t 0 = x := by
  simp [verticalPoint]

@[simp] theorem verticalPoint_apply_one (x t : ℝ) : verticalPoint x t 1 = t := by
  simp [verticalPoint]

theorem continuous_horizontalPoint (y : ℝ) : Continuous (horizontalPoint y) := by
  have h : Continuous fun t : ℝ => (![t, y] : Fin 2 → ℝ) := by fun_prop
  show Continuous fun t : ℝ => (WithLp.toLp 2 ![t, y] : Plane)
  exact (PiLp.continuous_toLp 2 fun _ : Fin 2 => ℝ).comp h

theorem continuous_verticalPoint (x : ℝ) : Continuous (verticalPoint x) := by
  have h : Continuous fun t : ℝ => (![x, t] : Fin 2 → ℝ) := by fun_prop
  show Continuous fun t : ℝ => (WithLp.toLp 2 ![x, t] : Plane)
  exact (PiLp.continuous_toLp 2 fun _ : Fin 2 => ℝ).comp h

theorem horizontal_eq_image (a b y : ℝ) :
    horizontal a b y = horizontalPoint y '' Set.Icc a b := by
  ext z
  simp only [horizontal, Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z 0, ⟨h1, h2⟩, PiLp.ext fun i => ?_⟩
    fin_cases i
    · simp
    · simp [h3]
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simpa using h1, by simpa using h2, by simp⟩

theorem vertical_eq_image (x a b : ℝ) :
    vertical x a b = verticalPoint x '' Set.Icc a b := by
  ext z
  simp only [vertical, Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z 1, ⟨h2, h3⟩, PiLp.ext fun i => ?_⟩
    fin_cases i
    · simp [h1]
    · simp
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨by simp, by simpa using h1, by simpa using h2⟩

theorem isCompact_horizontal (a b y : ℝ) : IsCompact (horizontal a b y) := by
  rw [horizontal_eq_image]
  exact isCompact_Icc.image (continuous_horizontalPoint y)

theorem isCompact_vertical (x a b : ℝ) : IsCompact (vertical x a b) := by
  rw [vertical_eq_image]
  exact isCompact_Icc.image (continuous_verticalPoint x)

theorem isPreconnected_horizontal (a b y : ℝ) : IsPreconnected (horizontal a b y) := by
  rw [horizontal_eq_image]
  exact isPreconnected_Icc.image _ (continuous_horizontalPoint y).continuousOn

theorem isPreconnected_vertical (x a b : ℝ) : IsPreconnected (vertical x a b) := by
  rw [vertical_eq_image]
  exact isPreconnected_Icc.image _ (continuous_verticalPoint x).continuousOn

/-! ### Finitely many cells meet a compact set off the singular set -/

/-- Local finiteness off `Ssing` plus compactness gives global finiteness: only finitely many cells
meet a compact set disjoint from `Ssing`. -/
theorem finite_hits_of_isCompact_of_notMem_sing {F : IndexedCells V} (sw : SingularWitness F)
    {L : Set Plane} (hcomp : IsCompact L) (havoid : ∀ z ∈ L, z ∉ sw.sing) :
    {v | Hits F L v}.Finite := by
  have hne : ∀ z ∈ L, ∃ U : Set Plane, U ∈ 𝓝 z ∧ {v | Hits F U v}.Finite :=
    fun z hz => sw.locallyFinite z (havoid z hz)
  choose! U hUmem hUfin using hne
  obtain ⟨t, htL, htcover⟩ := hcomp.elim_nhds_subcover U hUmem
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet
    (fun z hz => hUfin z (htL z (Finset.mem_coe.mp hz)))) ?_
  rintro v ⟨p, hpc, hpL⟩
  obtain ⟨z, hzt, hpz⟩ := Set.mem_iUnion₂.mp (htcover hpL)
  exact Set.mem_iUnion₂.mpr ⟨z, Finset.mem_coe.mpr hzt, ⟨p, hpc, hpz⟩⟩

/-! ### Connectivity of the cells met by a connected set off `Ssing ∪ V*` -/

/-- The cells meeting a preconnected set that avoids `Ssing ∪ V*` induce a connected subgraph.

The proof is the manuscript's: were the induced graph disconnected, the reachability class of one
vertex and its complement would cut the set into two nonempty disjoint relatively closed pieces.
Closedness uses the finiteness supplied by `hfin`; disjointness uses Definition 1.1(iv), since a
common point would lie in two distinct cells outside `Ssing ∪ V*` and hence force adjacency. -/
theorem segmentReachable_of_isPreconnected_of_avoids {F : IndexedCells V} (sw : SingularWitness F)
    {L : Set Plane} (hfin : {v | Hits F L v}.Finite) (hconn : IsPreconnected L)
    (havoid : ∀ z ∈ L, z ∉ sw.sing ∪ sw.vstar) :
    SegmentReachable F L := by
  classical
  haveI hsubfin : Finite {v // v ∈ {v | Hits F L v}} := hfin.to_subtype
  show (F.graph.toSimpleGraph.induce {v | Hits F L v}).Preconnected
  intro u₀ w₀
  by_contra hnr
  set R : Set {v // v ∈ {v | Hits F L v}} :=
    {q | (F.graph.toSimpleGraph.induce {v | Hits F L v}).Reachable u₀ q} with hRdef
  set FA : Set Plane := ⋃ q ∈ R, (F.cell (q : V) : Set Plane) with hFAdef
  set FB : Set Plane := ⋃ q ∈ Rᶜ, (F.cell (q : V) : Set Plane) with hFBdef
  have hFAclosed : IsClosed FA :=
    (Set.toFinite R).isClosed_biUnion fun q _ => (F.cell (q : V)).isCompact.isClosed
  have hFBclosed : IsClosed FB :=
    (Set.toFinite Rᶜ).isClosed_biUnion fun q _ => (F.cell (q : V)).isCompact.isClosed
  have hcover : L ⊆ FA ∪ FB := by
    intro z hz
    have hzs : z ∉ sw.sing := fun hc => havoid z hz (Or.inl hc)
    obtain ⟨v, hzv⟩ := Set.mem_iUnion.mp (sw.cover hzs)
    have hvH : v ∈ {v | Hits F L v} := ⟨z, hzv, hz⟩
    by_cases hq : (⟨v, hvH⟩ : {v // v ∈ {v | Hits F L v}}) ∈ R
    · exact Or.inl (Set.mem_biUnion hq hzv)
    · exact Or.inr (Set.mem_biUnion hq hzv)
  have hFAne : (L ∩ FA).Nonempty := by
    obtain ⟨p, hpc, hpL⟩ := (u₀.2 : Hits F L (u₀ : V))
    exact ⟨p, hpL, Set.mem_biUnion (show u₀ ∈ R from SimpleGraph.Reachable.refl u₀) hpc⟩
  have hFBne : (L ∩ FB).Nonempty := by
    obtain ⟨p, hpc, hpL⟩ := (w₀.2 : Hits F L (w₀ : V))
    exact ⟨p, hpL, Set.mem_biUnion (show w₀ ∈ Rᶜ from hnr) hpc⟩
  obtain ⟨p, hpL, hpA, hpB⟩ :=
    isPreconnected_closed_iff.mp hconn FA FB hFAclosed hFBclosed hcover hFAne hFBne
  obtain ⟨q, hqR, hpq⟩ := Set.mem_iUnion₂.mp hpA
  obtain ⟨q', hq'R, hpq'⟩ := Set.mem_iUnion₂.mp hpB
  have hne : (q : V) ≠ (q' : V) := by
    intro hEq
    exact hq'R ((Subtype.ext hEq : q = q') ▸ hqR)
  have hadj : F.graph.toSimpleGraph.Adj (q : V) (q' : V) :=
    sw.face p (havoid p hpL) _ _ hne hpq hpq'
  exact hq'R (hqR.trans (SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.mpr hadj)))

/-- **The geometric core of Proposition 2.1.** A compact preconnected subset of the plane avoiding
`Ssing ∪ V*` meets only finitely many cells, and those cells induce a connected subgraph. -/
theorem finite_and_segmentReachable_of_isCompact_of_isPreconnected {F : IndexedCells V}
    (sw : SingularWitness F) {L : Set Plane} (hcomp : IsCompact L) (hconn : IsPreconnected L)
    (havoid : ∀ z ∈ L, z ∉ sw.sing ∪ sw.vstar) :
    {v | Hits F L v}.Finite ∧ SegmentReachable F L := by
  have hfin := finite_hits_of_isCompact_of_notMem_sing sw hcomp
    fun z hz hc => havoid z hz (Or.inl hc)
  exact ⟨hfin, segmentReachable_of_isPreconnected_of_avoids sw hfin hconn havoid⟩

/-! ### Proposition 2.1 -/

/-- **Proposition 2.1 (Generic lines and finite boundaries).**  Under Definition 1.1 there are
Lebesgue-null sets `Nh, Nv ⊆ ℝ` such that for `y ∉ Nh` every horizontal segment `[a,b] × {y}` meets
finitely many cells and induces a connected subgraph, and symmetrically for `x ∉ Nv` and the
vertical segments `{x} × [a,b]`.

Both exceptional sets are produced once and work simultaneously for *all* segment endpoints, which
is what the AE-LC quantifier order requires and what Corollary 2.2 needs in order to control the
four sides of a rectangle at the same time. -/
theorem exists_null_sets_segment_finite_and_reachable [Countable V] {F : IndexedCells V}
    (h : GeometrySingular F) :
    ∃ Nh Nv : Set ℝ, MeasurableSet Nh ∧ volume Nh = 0 ∧ MeasurableSet Nv ∧ volume Nv = 0 ∧
      (∀ y ∉ Nh, ∀ a b : ℝ, a < b →
        {v | Hits F (horizontal a b y) v}.Finite ∧ SegmentReachable F (horizontal a b y)) ∧
      (∀ x ∉ Nv, ∀ a b : ℝ, a < b →
        {v | Hits F (vertical x a b) v}.Finite ∧ SegmentReachable F (vertical x a b)) := by
  obtain ⟨sw⟩ := h.nonempty_witness
  have hE : ∀ i : Fin 2, volume (coordProj i '' (sw.sing ∪ sw.vstar)) = 0 := by
    intro i
    rw [Set.image_union]
    refine measure_union_null (volume_image_coordProj_eq_zero i sw.hausdorff_sing) ?_
    exact (sw.countable_vstar.image (coordProj i)).measure_zero volume
  obtain ⟨Nh, hNhsub, hNhmeas, hNhnull⟩ := exists_measurable_superset_of_null (hE 1)
  obtain ⟨Nv, hNvsub, hNvmeas, hNvnull⟩ := exists_measurable_superset_of_null (hE 0)
  refine ⟨Nh, Nv, hNhmeas, hNhnull, hNvmeas, hNvnull, ?_, ?_⟩
  · intro y hy a b _
    refine finite_and_segmentReachable_of_isCompact_of_isPreconnected sw
      (isCompact_horizontal a b y) (isPreconnected_horizontal a b y) ?_
    rintro z ⟨-, -, hz1⟩ hzE
    exact hy (hNhsub ⟨z, hzE, hz1⟩)
  · intro x hx a b _
    refine finite_and_segmentReachable_of_isCompact_of_isPreconnected sw
      (isCompact_vertical x a b) (isPreconnected_vertical x a b) ?_
    rintro z ⟨hz0, -, -⟩ hzE
    exact hx (hNvsub ⟨z, hzE, hz0⟩)

/-- **Definition 1.1 implies AE-LC.**  This is what lets the existing corpus, whose environment
validity predicate `ReflectedGMS.Code.Valid` takes `AELineConnected` as a hypothesis, apply to the
singular-set configurations of the new manuscript. -/
theorem aeLineConnected_of_geometrySingular [Countable V] {F : IndexedCells V}
    (h : GeometrySingular F) : AELineConnected F := by
  obtain ⟨Nh, Nv, hNhmeas, hNhnull, hNvmeas, hNvnull, hh, hv⟩ :=
    exists_null_sets_segment_finite_and_reachable h
  rw [aeLineConnected_iff_exists_measurable_null_sets]
  exact ⟨Nh, Nv, hNhmeas, hNhnull, hNvmeas, hNvnull,
    fun y hy a b hab => (hh y hy a b hab).2, fun x hx a b hab => (hv x hx a b hab).2⟩

end ReflectedGMS

#print axioms ReflectedGMS.exists_null_sets_segment_finite_and_reachable
#print axioms ReflectedGMS.aeLineConnected_of_geometrySingular

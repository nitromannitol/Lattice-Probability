/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.GeneralNullBoundaries at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralGeometry
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities
import LatticeProb.Bonanno.ReflectedGMS.MeasureTheory.HausdorffPlane
import Mathlib.Util.AssertNoSorry

/-!
# Lemma 2.1 (null boundaries) of the general-cell manuscript

Manuscript: "Reflected scale-free invariance principle — cell configurations with singularities"
(`work/general/manuscript-text.txt`, lines 262–282).

**Lemma 2.1.**  Under Definition 1.1, distinct cell interiors are disjoint, every cell boundary has
zero area, and the uncovered set has zero one-dimensional Hausdorff measure.  In particular the cells
cover Lebesgue-almost every point.

These three facts were *clauses* of the earlier environment classes (`ReflectedGMS.Geometry`,
`ReflectedGMS.GeometrySingular`); for `ReflectedGMS.GeneralGeometry` they are derived, following the
manuscript:

* `GeneralGeometry.disjoint_interior` — a common interior point would give an open subset of
  `H ∩ K`, of positive area;
* `CellConfiguration.SingularSet.uncoveredSet_subset` / `hausdorffMeasure_uncoveredSet` — the
  uncovered set lies in `Ssing`;
* `CellConfiguration.SingularSet.frontier_subset` — the manuscript's inclusion
  `∂H ⊆ Ssing ∪ ⋃_{K ≠ H} (H ∩ K)`, from spatial local finiteness off `Ssing`, closedness of the
  cells, and the fact that `Ssing` has empty interior;
* `GeneralGeometry.volume_frontier` and `GeneralGeometry.volume_boundaryMask` — the resulting
  Lebesgue-nullity of every cell boundary and of the rooted-functional exception mask.

The implication `H¹ = 0 ⇒ area = 0` is `ReflectedGMS.volume_eq_zero_of_hausdorffMeasure_one`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace ReflectedGMS

namespace CellConfiguration

namespace SingularSet

variable {V : Type*} {C : CellConfiguration V}

/-- The singular set is Lebesgue-null. -/
theorem volume_sing (S : SingularSet C) : volume S.sing = 0 :=
  volume_eq_zero_of_hausdorffMeasure_one S.hausdorff_sing

/-- The singular set has empty interior. -/
theorem interior_sing_eq_empty (S : SingularSet C) : interior S.sing = ∅ := by
  by_contra h
  have hpos : 0 < volume S.sing :=
    Measure.measure_pos_of_nonempty_interior volume (Set.nonempty_iff_ne_empty.mpr h)
  rw [S.volume_sing] at hpos
  exact lt_irrefl 0 hpos

/-- The complement of the singular set is dense. -/
theorem dense_compl_sing (S : SingularSet C) : Dense S.singᶜ :=
  interior_eq_empty_iff_dense_compl.mp S.interior_sing_eq_empty

/-- **Lemma 2.1, uncovered set.**  Every uncovered point is singular. -/
theorem uncoveredSet_subset (S : SingularSet C) : uncoveredSet C.cellsOnly ⊆ S.sing := by
  intro z hz
  by_contra hzs
  exact hz (S.cover hzs)

/-- **Lemma 2.1, uncovered set.**  The uncovered set has zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_uncoveredSet (S : SingularSet C) :
    μH[1] (uncoveredSet C.cellsOnly) = 0 :=
  measure_mono_null S.uncoveredSet_subset S.hausdorff_sing

/-- The cells cover Lebesgue-almost every point. -/
theorem volume_uncoveredSet (S : SingularSet C) : volume (uncoveredSet C.cellsOnly) = 0 :=
  measure_mono_null S.uncoveredSet_subset S.volume_sing

/-- **The boundary inclusion of Lemma 2.1:** `∂H ⊆ Ssing ∪ ⋃_{K ≠ H} (H ∩ K)`.

Proof: let `z ∈ ∂H \ Ssing` lie in no other cell.  A neighbourhood `U` of `z` meets only finitely
many cells, so removing the finitely many cells `K ≠ H` meeting `U` from `interior U` leaves an open
set `O ∋ z`.  Every point of `O` off `Ssing` is covered, by a cell meeting `U`, hence by `H`.  As
`Ssing` has empty interior and `H` is closed, `O ⊆ H`, so `z ∈ interior H`, contradicting
`z ∈ ∂H`. -/
theorem frontier_subset (S : SingularSet C) (v : V) :
    frontier (C.cell v : Set Plane) ⊆
      S.sing ∪ ⋃ w, ⋃ (_ : w ≠ v), (C.cell v : Set Plane) ∩ (C.cell w : Set Plane) := by
  intro z hz
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hzs, hzK⟩ := hcon
  obtain ⟨U, hU, hUfin⟩ := S.locallyFinite z hzs
  have hclosed : IsClosed (C.cell v : Set Plane) := (C.cell v).isCompact.isClosed
  have hzv : z ∈ (C.cell v : Set Plane) := by
    have hzc := frontier_subset_closure hz
    rwa [hclosed.closure_eq] at hzc
  set T : Set V := {w | C.Hits U w ∧ w ≠ v} with hTdef
  have hTfin : T.Finite := hUfin.subset fun w hw => hw.1
  set O : Set Plane := interior U \ ⋃ w ∈ T, (C.cell w : Set Plane) with hOdef
  have hOopen : IsOpen O :=
    isOpen_interior.sdiff (hTfin.isClosed_biUnion fun w _ => (C.cell w).isCompact.isClosed)
  have hzO : z ∈ O := by
    refine ⟨mem_interior_iff_mem_nhds.mpr hU, fun hmem => ?_⟩
    obtain ⟨w, hwT, hzw⟩ := Set.mem_iUnion₂.mp hmem
    exact hzK (Set.mem_iUnion₂.mpr ⟨w, hwT.2, hzv, hzw⟩)
  have hOsub : O ∩ S.singᶜ ⊆ (C.cell v : Set Plane) := by
    rintro p ⟨hpO, hps⟩
    obtain ⟨w, hpw⟩ := Set.mem_iUnion.mp (S.cover hps)
    by_cases hwv : w = v
    · rw [← hwv]
      exact hpw
    · exact (hpO.2 (Set.mem_iUnion₂.mpr ⟨w, ⟨⟨p, hpw, interior_subset hpO.1⟩, hwv⟩, hpw⟩)).elim
  have hOv : O ⊆ (C.cell v : Set Plane) := by
    refine (S.dense_compl_sing.open_subset_closure_inter hOopen).trans ?_
    simpa [hclosed.closure_eq] using closure_mono hOsub
  exact hz.2 (mem_interior.mpr ⟨O, hOv, hOopen, hzO⟩)

end SingularSet

end CellConfiguration

open CellConfiguration

namespace GeneralGeometry

variable {V : Type*} {C : CellConfiguration V}

/-- **Lemma 2.1, interiors.**  Distinct cell interiors are disjoint. -/
theorem disjoint_interior (h : GeneralGeometry C) :
    ∀ ⦃v w⦄, v ≠ w →
      Disjoint (interior (C.cell v : Set Plane)) (interior (C.cell w : Set Plane)) := by
  intro v w hvw
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  have hpos : 0 < volume (interior (C.cell v : Set Plane) ∩ interior (C.cell w : Set Plane)) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume (Set.nonempty_iff_ne_empty.mpr hne)
  exact hpos.ne' (measure_mono_null (Set.inter_subset_inter interior_subset interior_subset)
    (h.volume_inter hvw))

/-- **Lemma 2.1, uncovered set**, for a configuration satisfying Definition 1.1. -/
theorem hausdorffMeasure_uncoveredSet (h : GeneralGeometry C) :
    μH[1] (uncoveredSet C.cellsOnly) = 0 := by
  obtain ⟨S, -⟩ := h.exists_singularSet
  exact S.hausdorffMeasure_uncoveredSet

/-- The cells cover Lebesgue-almost every point. -/
theorem volume_uncoveredSet (h : GeneralGeometry C) : volume (uncoveredSet C.cellsOnly) = 0 :=
  volume_eq_zero_of_hausdorffMeasure_one h.hausdorffMeasure_uncoveredSet

/-- **Lemma 2.1, boundaries.**  Every cell boundary has zero area. -/
theorem volume_frontier [Countable V] (h : GeneralGeometry C) :
    ∀ v, volume (frontier (C.cell v : Set Plane)) = 0 := by
  intro v
  obtain ⟨S, -⟩ := h.exists_singularSet
  refine measure_mono_null (S.frontier_subset v) (measure_union_null S.volume_sing ?_)
  exact measure_iUnion_null fun w => measure_iUnion_null fun hw => h.volume_inter (Ne.symm hw)

/-- The rooted-functional exception mask (all cell boundaries together with the uncovered set) is
Lebesgue-null. -/
theorem volume_boundaryMask [Countable V] (h : GeneralGeometry C) :
    volume (RootDensities.boundaryMask C.cellsOnly) = 0 := by
  show volume ((⋃ v, frontier (C.cell v : Set Plane)) ∪ uncoveredSet C.cellsOnly) = 0
  exact measure_union_null (measure_iUnion_null fun v => h.volume_frontier v)
    h.volume_uncoveredSet

end GeneralGeometry

end ReflectedGMS

assert_no_sorry ReflectedGMS.CellConfiguration.SingularSet.frontier_subset
assert_no_sorry ReflectedGMS.CellConfiguration.SingularSet.uncoveredSet_subset
assert_no_sorry ReflectedGMS.CellConfiguration.SingularSet.hausdorffMeasure_uncoveredSet
assert_no_sorry ReflectedGMS.GeneralGeometry.disjoint_interior
assert_no_sorry ReflectedGMS.GeneralGeometry.volume_frontier
assert_no_sorry ReflectedGMS.GeneralGeometry.volume_boundaryMask
#print axioms ReflectedGMS.CellConfiguration.SingularSet.frontier_subset
#print axioms ReflectedGMS.CellConfiguration.SingularSet.uncoveredSet_subset
#print axioms ReflectedGMS.CellConfiguration.SingularSet.hausdorffMeasure_uncoveredSet
#print axioms ReflectedGMS.GeneralGeometry.disjoint_interior
#print axioms ReflectedGMS.GeneralGeometry.volume_frontier
#print axioms ReflectedGMS.GeneralGeometry.volume_boundaryMask

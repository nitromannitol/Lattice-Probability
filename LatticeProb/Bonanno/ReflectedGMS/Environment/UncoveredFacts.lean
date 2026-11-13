/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.UncoveredFacts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GenericLines
import LatticeProb.Bonanno.ReflectedGMS.MeasureTheory.HausdorffPlane

/-!
# Consequences of the covering clause of `Geometry`

The covering clause of `ReflectedGMS.Geometry` asks that the uncovered set be `H¹`-null.  Under the
earlier manuscript's hypothesis the uncovered set is empty, so all of the following are vacuous
there; under the singular-set manuscript's Definition 1.1 the uncovered set is contained in `Ssing`
and these are the facts that replace "every point lies in a cell".

Three are used repeatedly:

* `volume_uncoveredSet` — the uncovered set is Lebesgue-null, so it has empty interior and its
  complement is dense.  This rescues every argument that needs a covered point *near* a given point
  rather than *at* it.
* `exists_mem_cell_of_isOpen` — every nonempty open set contains a point lying in a cell.
* `volume_coordProj_uncoveredSet` — the coordinate projections of the uncovered set are Lebesgue-null
  in `ℝ`, so almost every axis-parallel line misses the uncovered set *entirely* and every point of
  such a line lies in a cell (`exists_cell_of_coordProj_notMem`).  This is the reason the covering
  clause is stated with `H¹` rather than with plane Lebesgue measure: a Lebesgue-null planar set can
  project onto a set of positive measure.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS

variable {V : Type*} [Countable V] {F : IndexedCells V}

/-- The covering clause of `Geometry`, named. -/
theorem hausdorffMeasure_uncoveredSet (hF : Geometry F) : μH[1] (uncoveredSet F) = 0 :=
  hF.2.2.2.2.1

/-- The uncovered set is Lebesgue-null. -/
theorem volume_uncoveredSet (hF : Geometry F) : volume (uncoveredSet F) = 0 :=
  volume_eq_zero_of_hausdorffMeasure_one (hausdorffMeasure_uncoveredSet hF)

/-- A point outside the uncovered set lies in a cell. -/
theorem exists_mem_cell_of_notMem_uncoveredSet {z : Plane} (hz : z ∉ uncoveredSet F) :
    ∃ v, z ∈ (F.cell v : Set Plane) := by
  refine Set.mem_iUnion.mp ?_
  by_contra h
  exact hz h

/-- The uncovered set has empty interior. -/
theorem interior_uncoveredSet_eq_empty (hF : Geometry F) : interior (uncoveredSet F) = ∅ := by
  by_contra h
  have hpos : 0 < volume (uncoveredSet F) :=
    Measure.measure_pos_of_nonempty_interior volume (Set.nonempty_iff_ne_empty.mpr h)
  rw [volume_uncoveredSet hF] at hpos
  exact lt_irrefl 0 hpos

/-- The covered points are dense. -/
theorem dense_compl_uncoveredSet (hF : Geometry F) : Dense (uncoveredSet F)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (interior_uncoveredSet_eq_empty hF)

/-- Every nonempty open set contains a point lying in a cell. -/
theorem exists_mem_cell_of_isOpen (hF : Geometry F) {U : Set Plane} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ z ∈ U, ∃ v, z ∈ (F.cell v : Set Plane) := by
  -- `Dense.exists_mem_open` returns membership in the DENSE set first, then in `U`.
  obtain ⟨z, hzc, hzU⟩ := (dense_compl_uncoveredSet hF).exists_mem_open hU hne
  exact ⟨z, hzU, exists_mem_cell_of_notMem_uncoveredSet hzc⟩

/-- An open set is contained in the closure of its covered part. -/
theorem subset_closure_inter_compl_uncoveredSet (hF : Geometry F) {U : Set Plane} (hU : IsOpen U) :
    U ⊆ closure (U ∩ (uncoveredSet F)ᶜ) :=
  (dense_compl_uncoveredSet hF).open_subset_closure_inter hU

/-- A closed set containing the covered part of an open set contains the whole open set.  This is the
form the ball/cell arguments use: they establish `ball x δ \ uncovered ⊆ cell v` and conclude
`ball x δ ⊆ cell v`, cells being compact and hence closed. -/
theorem subset_of_isClosed_of_inter_compl_subset (hF : Geometry F) {U C : Set Plane}
    (hU : IsOpen U) (hC : IsClosed C) (h : U ∩ (uncoveredSet F)ᶜ ⊆ C) : U ⊆ C := by
  refine (subset_closure_inter_compl_uncoveredSet hF hU).trans ?_
  simpa [hC.closure_eq] using closure_mono h

/-- The coordinate projections of the uncovered set are Lebesgue-null. -/
theorem volume_coordProj_uncoveredSet (hF : Geometry F) (i : Fin 2) :
    volume (coordProj i '' uncoveredSet F) = 0 :=
  volume_image_coordProj_eq_zero i (hausdorffMeasure_uncoveredSet hF)

/-- Off a Lebesgue-null set of offsets, an entire axis-parallel line is covered: every point of the
plane whose `i`-th coordinate avoids the projected uncovered set lies in a cell. -/
theorem exists_cell_of_coordProj_notMem {i : Fin 2} {z : Plane}
    (hz : coordProj i z ∉ coordProj i '' uncoveredSet F) :
    ∃ v, z ∈ (F.cell v : Set Plane) :=
  exists_mem_cell_of_notMem_uncoveredSet fun hmem => hz ⟨z, hmem, rfl⟩

end ReflectedGMS

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.EndSpatialImageGeneral at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeneralMainStatements
import Mathlib.Util.AssertNoSorry

/-!
# Spatial images of graph ends for the slim singular witness (Proposition 2.6)

This file proves the first sentence of Theorem 1.3(b) of the general-cell singular-set manuscript
(`work/general/manuscript-text.txt`, Proposition 2.6, lines 359–394):
`GeneralMainStatements.EndSpatialImageConclusions F` — for **every** slim singular witness
`w : SingularSet F.toCellConfiguration` and every graph end `e`, the nested spherical closures of
the end's cell components shrink to the single point `endImage F e`, which lies in
`w.sing ∪ {∞}`, is `∞` exactly for the ends at spatial infinity, and depends continuously on the end.

## Reuse

The proof is the one of `ReflectedGMS/Geometry/EndSpatialImage.lean`, whose core results were
generalized in place (suffix `_of_cells`) to the hypotheses the argument actually uses:

* about the cells, `EndSpatialImage.ConnectedAdjacentCells F` — every cell is connected and adjacent
  cells intersect;
* about the singular set, `μH[1] S = 0` and `EndSpatialImage.LocallyFiniteOff F S`.

A slim witness supplies the last two verbatim (`w.hausdorff_sing`, `w.locallyFinite`); its
closedness and covering clauses are not needed, and it has no face rule and no exceptional set `V*`
— matching the manuscript's remark that Proposition 2.6 "uses no face-incidence rule".  Graph
connectedness and local finiteness are not used either; they enter only through the anti-vacuity
statement `nonempty_graphEnd_of_infinite_of_geometry` (ends exist at all).

## Main results

* `endSpatialImageConclusions_of_connectedAdjacentCells` — the conclusions from the two cell facts
  alone.
* `endSpatialImageConclusions_of_geometry` — the packet's target, from `Geometry F`.
* `endSpatialImageConclusions_of_generalGeometry` — from Definition 1.1 + (LCS) of the general
  manuscript (`GeneralGeometry F.toCellConfiguration`).
-/

set_option autoImplicit false

open MeasureTheory

namespace ReflectedGMS.GeneralMainStatements

open EndSpatialImage SpatialEnds CellConfiguration

/-- **Proposition 2.6 / Theorem 1.3(b), first sentence**, from the two facts about the cells that
the argument uses: cells are connected and adjacent cells intersect.  The singular set enters only
through the slim witness `w`, via `μH[1] w.sing = 0` and local finiteness off `w.sing`. -/
theorem endSpatialImageConclusions_of_connectedAdjacentCells {V : Type*} [Countable V]
    {F : IndexedCells V} (hc : ConnectedAdjacentCells F) : EndSpatialImageConclusions F := by
  intro w e
  have hS : μH[(1 : ℝ)] w.sing = 0 := w.hausdorff_sing
  have hlf : LocallyFiniteOff F w.sing := w.locallyFinite
  refine ⟨endImageSet_eq_singleton_of_cells hc hS hlf e, endImage_mem_of_locallyFiniteOff hlf e,
    endImage_eq_infty_iff_of_cells hc hS hlf e, ?_⟩
  intro U hU hmem
  exact exists_finset_forall_endImage_mem_of_cells hc hS hlf e hU hmem

/-- **Proposition 2.6 / Theorem 1.3(b), first sentence**, for a configuration satisfying the
geometric conditions `Geometry F` (in particular for `decode e`, `e : Env`), and for every slim
singular witness. -/
theorem endSpatialImageConclusions_of_geometry {V : Type*} [Countable V]
    {F : IndexedCells V} (hG : Geometry F) : EndSpatialImageConclusions F :=
  endSpatialImageConclusions_of_connectedAdjacentCells (connectedAdjacentCells_of_geometry hG)

/-- The cell facts used by Proposition 2.6 follow from Definition 1.1 + (LCS) of the general-cell
manuscript. -/
theorem connectedAdjacentCells_of_generalGeometry {V : Type*} {F : IndexedCells V}
    (h : GeneralGeometry F.toCellConfiguration) : ConnectedAdjacentCells F :=
  ⟨h.isConnected, h.adj_inter_nonempty⟩

/-- **Proposition 2.6 / Theorem 1.3(b), first sentence**, under the manuscript's own hypotheses:
Definition 1.1 + (LCS) for a configuration whose graph is locally finite (so that it is an
`IndexedCells`). -/
theorem endSpatialImageConclusions_of_generalGeometry {V : Type*} [Countable V]
    {F : IndexedCells V} (h : GeneralGeometry F.toCellConfiguration) :
    EndSpatialImageConclusions F :=
  endSpatialImageConclusions_of_connectedAdjacentCells (connectedAdjacentCells_of_generalGeometry h)

/-- **Anti-vacuity.**  Under `Geometry` with an infinite vertex set there is at least one graph end,
so `EndSpatialImageConclusions` is not a statement about an empty index.  (The type variable is at
`Type` because that is the universe of mathlib's `SimpleGraph.nonempty_ends_of_infinite`.) -/
theorem nonempty_graphEnd_of_infinite_of_geometry {W : Type} [Countable W] [Infinite W]
    {F : IndexedCells W} (h : Geometry F) : (GraphEnd F).Nonempty := by
  have : Fact F.graph.toSimpleGraph.Preconnected := ⟨h.2.2.2.2.2.1.preconnected⟩
  have : F.graph.toSimpleGraph.LocallyFinite := fun v => (h.2.2.2.2.2.2.1 v).fintype
  exact SimpleGraph.nonempty_ends_of_infinite _

end ReflectedGMS.GeneralMainStatements

assert_no_sorry ReflectedGMS.GeneralMainStatements.endSpatialImageConclusions_of_connectedAdjacentCells
assert_no_sorry ReflectedGMS.GeneralMainStatements.endSpatialImageConclusions_of_geometry
assert_no_sorry ReflectedGMS.GeneralMainStatements.endSpatialImageConclusions_of_generalGeometry
assert_no_sorry ReflectedGMS.GeneralMainStatements.nonempty_graphEnd_of_infinite_of_geometry

#print axioms ReflectedGMS.GeneralMainStatements.endSpatialImageConclusions_of_connectedAdjacentCells
#print axioms ReflectedGMS.GeneralMainStatements.endSpatialImageConclusions_of_geometry
#print axioms ReflectedGMS.GeneralMainStatements.endSpatialImageConclusions_of_generalGeometry
#print axioms ReflectedGMS.GeneralMainStatements.nonempty_graphEnd_of_infinite_of_geometry

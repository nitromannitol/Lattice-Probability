/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.SingularGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Geometry
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Face configurations with a singular set

This file states **Definition 1.1** of the singular-set manuscript ("An invariance principle for
reflected random walks with spatial singularities"), which generalises the covering hypothesis of
`ReflectedGMS.Geometry`.

The manuscript's Definition 1.1 imposes:

* (i) every cell has nonempty interior and Lebesgue-null boundary, and distinct cells have disjoint
  interiors (cells are compact and connected by the ambient `IndexedCells` conventions);
* (ii) there is a **closed** set `Ssing` with `H¹(Ssing) = 0` such that `ℂ \ Ssing ⊆ ⋃ H`, and every
  point of `ℂ \ Ssing` has a neighbourhood meeting only finitely many cells.  No covering assumption
  is imposed at points of `Ssing`;
* (iii) the cell adjacency graph is connected and locally finite; adjacent cells are distinct and
  intersect, with finite strictly positive symmetric conductances;
* (iv) there is a **countable** set `V* ⊆ ℂ` such that whenever `z ∉ Ssing ∪ V*` lies in two distinct
  cells, those cells are adjacent.

The manuscript is explicit (page 2) that `Ssing` and `V*` are *geometric witnesses*: they are
existentially quantified and used pathwise, and they are **not** additional random marks — only the
cell configuration and its conductances are re-rooted in the mass-transport assumption.  That is why
`SingularWitness` is bundled under `Nonempty` in `GeometrySingular` rather than carried as data on
the environment.

The two structural clauses (i) and (iii) are shared verbatim with `ReflectedGMS.Geometry`; only the
covering clause differs, and (ii)'s local finiteness and (iv) are new.

**Fidelity note on (iv).** The manuscript says "whenever `z ∉ Ssing ∪ V*` and `z ∈ H ∩ K` for
*distinct cells*, `H ∼ K`", whereas `face` below quantifies over distinct *labels* `v ≠ w`.  These
agree: clause (i) makes the interiors of distinct labels disjoint and every cell's interior nonempty,
so two distinct labels cannot carry the same cell.  The Lean clause is therefore neither weaker nor
stronger than the manuscript's.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace ReflectedGMS

/-- A geometric witness for Definition 1.1(ii) and (iv): the singular set `Ssing`, the countable
exceptional set `V*`, and the four properties they carry.

`hausdorff_sing` is one-dimensional Hausdorff measure zero, which is strictly stronger than
Lebesgue-null and is what the generic-line and end-image arguments consume. -/
structure SingularWitness {V : Type*} (F : IndexedCells V) where
  /-- The singular set `Ssing` of Definition 1.1(ii). -/
  sing : Set Plane
  /-- The countable exceptional set `V*` of Definition 1.1(iv). -/
  vstar : Set Plane
  /-- `Ssing` is closed. -/
  isClosed_sing : IsClosed sing
  /-- `H¹(Ssing) = 0`. -/
  hausdorff_sing : μH[1] sing = 0
  /-- `V*` is countable. -/
  countable_vstar : vstar.Countable
  /-- Coverage off the singular set: `ℂ \ Ssing ⊆ ⋃ H`. -/
  cover : sing ᶜ ⊆ ⋃ v, (F.cell v : Set Plane)
  /-- Spatial local finiteness away from the singular set: every `z ∉ Ssing` has a neighbourhood
  meeting only finitely many cells. -/
  locallyFinite : ∀ z ∉ sing, ∃ U ∈ 𝓝 z, {v | Hits F U v}.Finite
  /-- Local face adjacency, Definition 1.1(iv): off `Ssing ∪ V*`, two distinct cells sharing a point
  are adjacent. -/
  face : ∀ z ∉ sing ∪ vstar, ∀ v w : V, v ≠ w →
    z ∈ (F.cell v : Set Plane) → z ∈ (F.cell w : Set Plane) →
    F.graph.toSimpleGraph.Adj v w

/-- **Definition 1.1**: a face configuration with a singular set.

Clauses (i) and (iii) are exactly those of `ReflectedGMS.Geometry`; the covering clause
`(⋃ v, cell v) = Set.univ` of `Geometry` is replaced by the existence of a `SingularWitness`, which
carries the weaker covering statement together with (ii)'s local finiteness and (iv). -/
def GeometrySingular {V : Type*} [Countable V] (F : IndexedCells V) : Prop :=
  (∀ v, IsConnected (F.cell v : Set Plane)) ∧
    (∀ v, (interior (F.cell v : Set Plane)).Nonempty) ∧
    (∀ v, volume (frontier (F.cell v : Set Plane)) = 0) ∧
    (∀ ⦃v w⦄, v ≠ w →
      Disjoint (interior (F.cell v : Set Plane)) (interior (F.cell w : Set Plane))) ∧
    Nonempty (SingularWitness F) ∧
    F.graph.toSimpleGraph.Connected ∧
    (∀ v, (F.graph.toSimpleGraph.neighborSet v).Finite) ∧
    (∀ ⦃v w⦄, F.graph.toSimpleGraph.Adj v w →
      ((F.cell v : Set Plane) ∩ (F.cell w : Set Plane)).Nonempty)

namespace GeometrySingular

variable {V : Type*} [Countable V] {F : IndexedCells V}

theorem isConnected (h : GeometrySingular F) : ∀ v, IsConnected (F.cell v : Set Plane) := h.1

theorem interior_nonempty (h : GeometrySingular F) :
    ∀ v, (interior (F.cell v : Set Plane)).Nonempty := h.2.1

theorem volume_frontier (h : GeometrySingular F) :
    ∀ v, volume (frontier (F.cell v : Set Plane)) = 0 := h.2.2.1

theorem disjoint_interior (h : GeometrySingular F) :
    ∀ ⦃v w⦄, v ≠ w →
      Disjoint (interior (F.cell v : Set Plane)) (interior (F.cell w : Set Plane)) := h.2.2.2.1

theorem nonempty_witness (h : GeometrySingular F) : Nonempty (SingularWitness F) := h.2.2.2.2.1

theorem connected (h : GeometrySingular F) : F.graph.toSimpleGraph.Connected := h.2.2.2.2.2.1

theorem neighborSet_finite (h : GeometrySingular F) :
    ∀ v, (F.graph.toSimpleGraph.neighborSet v).Finite := h.2.2.2.2.2.2.1

theorem adj_inter_nonempty (h : GeometrySingular F) :
    ∀ ⦃v w⦄, F.graph.toSimpleGraph.Adj v w →
      ((F.cell v : Set Plane) ∩ (F.cell w : Set Plane)).Nonempty := h.2.2.2.2.2.2.2

end GeometrySingular

end ReflectedGMS

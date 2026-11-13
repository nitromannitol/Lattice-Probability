/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.CodeGeneralValid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralGenericLines
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLaws
import Mathlib.Util.AssertNoSorry

/-!
# Definition 1.1 + (LCS) + finite rows ⇒ the corpus' environment validity

The earlier environment class `ReflectedGMS.Code.Valid` requires the eight clauses of
`ReflectedGMS.Geometry` (among them null boundaries, disjoint interiors, graph connectedness and graph
local finiteness) and `ReflectedGMS.AELineConnected`.  For a configuration satisfying Definition 1.1
and (LCS) of the general-cell manuscript (`ReflectedGMS.GeneralGeometry`), all of these except graph
local finiteness are *derived*:

* null boundaries and disjoint interiors — Lemma 2.1 (`Environment/GeneralNullBoundaries`);
* `H¹`-null uncovered set — Lemma 2.1;
* graph connectedness and almost-everywhere line connectivity — Proposition 2.3
  (`Environment/GeneralGenericLines`).

Graph local finiteness is the manuscript's Lemma 2.5 (derived there from mass transport and (FE));
here it enters as the hypothesis `FiniteRows r`, and `Code.finiteRows_of_valid` shows it is also
necessary.

Main results: `GeneralGeometry.geometry_toIndexedCells`, `Code.valid_of_validGeneral`,
`Code.finiteRows_of_valid`.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS

open CellConfiguration

namespace GeneralGeometry

variable {V : Type*} {C : CellConfiguration V}

/-- With finite rows, every cell has finitely many neighbours in the decoded conductance graph. -/
theorem neighborSet_finite_toIndexedCells (hfin : C.LocallyFiniteGraph) (v : V) :
    ((C.toIndexedCells hfin).graph.toSimpleGraph.neighborSet v).Finite :=
  (hfin v).subset fun _ hw => (show 0 < C.c v _ from hw).ne'

/-- **Definition 1.1 + (LCS) + graph local finiteness ⇒ `Geometry`.**  All eight clauses of the
corpus' geometric conditions hold for the configuration viewed as an `IndexedCells`. -/
theorem geometry_toIndexedCells [Countable V] (h : GeneralGeometry C)
    (hfin : C.LocallyFiniteGraph) : Geometry (C.toIndexedCells hfin) :=
  ⟨h.isConnected, h.interior_nonempty, h.volume_frontier, h.disjoint_interior,
    h.hausdorffMeasure_uncoveredSet, h.graph_connected, neighborSet_finite_toIndexedCells hfin,
    h.adj_inter_nonempty⟩

end GeneralGeometry

namespace Code

/-- Finite code rows make the raw configuration graph locally finite. -/
theorem locallyFiniteGraph_rawConfig {r : RawCode} (hr : RawAdmissible r) (hfin : FiniteRows r) :
    (rawConfig r hr).LocallyFiniteGraph :=
  fun v => (hfin v.val).preimage Subtype.val_injective.injOn

/-- The decoded network of a finite-row code is the raw configuration viewed as an
`IndexedCells`. -/
theorem decodeRaw_eq_toIndexedCells {r : RawCode} (hr : RawAdmissible r) (hfin : FiniteRows r) :
    decodeRaw r ((admissibleConductance_iff r).2 ⟨hr, hfin⟩) =
      (rawConfig r hr).toIndexedCells (locallyFiniteGraph_rawConfig hr hfin) :=
  rfl

/-- **General validity with finite rows implies the corpus' validity.** -/
theorem valid_of_validGeneral {r : RawCode} (h : ValidGeneral r) (hfin : FiniteRows r) :
    Valid r := by
  obtain ⟨hr, hgeom, hlab⟩ := h
  exact ⟨(admissibleConductance_iff r).2 ⟨hr, hfin⟩,
    hgeom.geometry_toIndexedCells (locallyFiniteGraph_rawConfig hr hfin),
    hgeom.aeLineConnected_toIndexedCells (locallyFiniteGraph_rawConfig hr hfin), hlab⟩

/-- Valid codes have finite rows. -/
theorem finiteRows_of_valid {r : RawCode} (h : Valid r) : FiniteRows r := by
  obtain ⟨hadm, -⟩ := h
  exact hadm.finiteRow

end Code

end ReflectedGMS

assert_no_sorry ReflectedGMS.GeneralGeometry.geometry_toIndexedCells
assert_no_sorry ReflectedGMS.Code.valid_of_validGeneral
assert_no_sorry ReflectedGMS.Code.finiteRows_of_valid
#print axioms ReflectedGMS.GeneralGeometry.geometry_toIndexedCells
#print axioms ReflectedGMS.Code.valid_of_validGeneral
#print axioms ReflectedGMS.Code.finiteRows_of_valid

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.GeneralGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.AELineConnectivity
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Definition 1.1 and (LCS) of the general-cell singular-set manuscript

Manuscript: "Reflected scale-free invariance principle — cell configurations with singularities"
(`work/general/manuscript.pdf`, text in `work/general/manuscript-text.txt`, lines 53–80).

**Definition 1.1 (Cell configurations with a singular set).**  A countably infinite collection of
compact connected subsets of `ℂ`, an adjacency relation `∼` and conductances `c`, such that

* (i) each cell has nonempty interior, and `Area(H ∩ K) = 0` for distinct cells;
* (ii) there is a closed set `Ssing` with `H¹(Ssing) = 0` and `ℂ \ Ssing ⊆ ⋃ H`, and every
  `z ∉ Ssing` has a neighbourhood meeting only finitely many cells;
* (iii) `∼` is symmetric, `H ∼ K ⇒ H ≠ K ∧ H ∩ K ≠ ∅`, and `c(H,K) = c(K,H) ∈ (0,∞)` on adjacent
  pairs.

**(LCS).**  `H(L)` is connected for every horizontal or vertical compact segment `L ⊂ ℂ \ Ssing`,
with the **same** witness `Ssing` as in (ii).

What is deliberately **absent**, as in the manuscript: no face/incidence rule (intersecting cells
need not be adjacent), no exceptional vertex set `V*`, no assumed graph connectedness, and no assumed
graph local finiteness — the manuscript derives connectedness (Proposition 2.3) and local finiteness
(Lemma 2.5, from mass transport and (FE)).  Null boundaries and disjoint interiors are likewise
derived (Lemma 2.1).

Because graph local finiteness is not assumed, the conductance array cannot be packaged as a
`ReflectedWalk.ConductanceGraph` (whose rows must be summable).  `CellConfiguration` is therefore
the cells together with a symmetric, nonnegative, loop-free real array, with **no** summability.
Adjacency is positivity of the conductance, exactly as for `ConductanceGraph`; this encodes
(iii): symmetry is `c_symm`, `H ∼ K ⇒ H ≠ K` holds at the level of labels by `c_self` (and at the
level of cells because distinct labels carry distinct cells, by (i)), and adjacent pairs carry a
real, hence finite, strictly positive conductance.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace ReflectedGMS

/-- A countable cell family with a symmetric, nonnegative, loop-free real conductance array.
No row is assumed summable or finitely supported. -/
structure CellConfiguration (V : Type*) where
  /-- The compact cells. -/
  cell : V → TopologicalSpace.NonemptyCompacts Plane
  /-- The conductance of the pair; `0` exactly off the adjacency relation. -/
  c : V → V → ℝ
  c_symm : ∀ x y, c x y = c y x
  c_nonneg : ∀ x y, 0 ≤ c x y
  c_self : ∀ x, c x x = 0

namespace CellConfiguration

variable {V : Type*} (C : CellConfiguration V)

/-- The adjacency graph: `H ∼ K` exactly when `c(H,K) > 0`. -/
def graph : SimpleGraph V where
  Adj x y := 0 < C.c x y
  symm := ⟨fun x y (h : 0 < C.c x y) => show 0 < C.c y x by rw [C.c_symm]; exact h⟩
  loopless := ⟨fun x (h : 0 < C.c x x) => by rw [C.c_self] at h; exact lt_irrefl _ h⟩

@[simp] theorem graph_adj {x y : V} : C.graph.Adj x y ↔ 0 < C.c x y := Iff.rfl

/-- The cell of `v` meets `A`. -/
def Hits (A : Set Plane) (v : V) : Prop := ((C.cell v : Set Plane) ∩ A).Nonempty

/-- The induced graph `H(A)` on the cells meeting `A` is connected by finite graph paths.
It is stated as `Preconnected`; for a nonempty set of covered points `H(A)` is nonempty, so this is
the manuscript's connectedness. -/
def InducedConnected (A : Set Plane) : Prop :=
  (C.graph.induce {v | C.Hits A v}).Preconnected

/-- Graph local finiteness: every cell has finitely many neighbours.  **Not** a hypothesis of the
general theorems; it is derived (Lemma 2.5). -/
def LocallyFiniteGraph : Prop := ∀ v, (Function.support (C.c v)).Finite

/-- Forget conductances: the same cells with the zero conductance array, as an `IndexedCells`, so
that the purely cell-geometric notions (`uncoveredSet`, `boundaryMask`, `rootAt`) can be reused. -/
def cellsOnly : IndexedCells V where
  cell := C.cell
  graph :=
    { c := fun _ _ => 0
      c_symm := fun _ _ => rfl
      c_nonneg := fun _ _ => le_rfl
      c_self := fun _ => rfl
      summable_c := fun _ => summable_zero }

/-- With locally finite rows the configuration is an `IndexedCells`. -/
def toIndexedCells (h : C.LocallyFiniteGraph) : IndexedCells V where
  cell := C.cell
  graph :=
    { c := C.c
      c_symm := C.c_symm
      c_nonneg := C.c_nonneg
      c_self := C.c_self
      summable_c := fun v => summable_of_hasFiniteSupport (h v) }

/-- **Definition 1.1(ii)**: a singular-set witness.  Only the singular set and the two covering /
local-finiteness properties; no exceptional vertex set and no face rule. -/
structure SingularSet {V : Type*} (C : CellConfiguration V) where
  /-- The singular set `Ssing`. -/
  sing : Set Plane
  isClosed_sing : IsClosed sing
  /-- `H¹(Ssing) = 0`. -/
  hausdorff_sing : μH[1] sing = 0
  /-- `ℂ \ Ssing ⊆ ⋃ H`. -/
  cover : singᶜ ⊆ ⋃ v, (C.cell v : Set Plane)
  /-- Every `z ∉ Ssing` has a neighbourhood meeting only finitely many cells. -/
  locallyFinite : ∀ z ∉ sing, ∃ U ∈ 𝓝 z, {v | C.Hits U v}.Finite

/-- **(LCS)**: `H(L)` is connected for every horizontal or vertical compact segment `L` disjoint
from `S`.  Endpoints are arbitrary reals (degenerate segments included, which the manuscript notes
gives the same condition; `a > b` gives the empty set, for which the clause is vacuous). -/
def LineConnectedOff (S : Set Plane) : Prop :=
  (∀ a b y : ℝ, Disjoint (horizontal a b y) S → C.InducedConnected (horizontal a b y)) ∧
    ∀ x a b : ℝ, Disjoint (vertical x a b) S → C.InducedConnected (vertical x a b)

end CellConfiguration

open CellConfiguration

/-- **Definition 1.1 together with (LCS)**, with one witness `Ssing` serving both.

Clause order: cells connected; interiors nonempty; distinct cells meet in a Lebesgue-null set; a
singular witness for which (LCS) holds; adjacent cells intersect.  (Compactness is carried by
`NonemptyCompacts`; symmetry, loop-freeness and finite positive conductances by
`CellConfiguration`.) -/
def GeneralGeometry {V : Type*} (C : CellConfiguration V) : Prop :=
  (∀ v, IsConnected (C.cell v : Set Plane)) ∧
    (∀ v, (interior (C.cell v : Set Plane)).Nonempty) ∧
    (∀ ⦃v w⦄, v ≠ w → volume ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)) = 0) ∧
    (∃ S : SingularSet C, C.LineConnectedOff S.sing) ∧
    (∀ ⦃v w⦄, C.graph.Adj v w → ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)).Nonempty)

/-- The conductance datum of an `IndexedCells`, forgetting row summability. -/
def IndexedCells.toCellConfiguration {V : Type*} (F : IndexedCells V) : CellConfiguration V where
  cell := F.cell
  c := F.graph.c
  c_symm := F.graph.c_symm
  c_nonneg := F.graph.c_nonneg
  c_self := F.graph.c_self

namespace GeneralGeometry

variable {V : Type*} {C : CellConfiguration V}

theorem isConnected (h : GeneralGeometry C) : ∀ v, IsConnected (C.cell v : Set Plane) := h.1

theorem interior_nonempty (h : GeneralGeometry C) :
    ∀ v, (interior (C.cell v : Set Plane)).Nonempty := h.2.1

theorem volume_inter (h : GeneralGeometry C) :
    ∀ ⦃v w⦄, v ≠ w → volume ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)) = 0 := h.2.2.1

theorem exists_singularSet (h : GeneralGeometry C) :
    ∃ S : SingularSet C, C.LineConnectedOff S.sing := h.2.2.2.1

theorem adj_inter_nonempty (h : GeneralGeometry C) :
    ∀ ⦃v w⦄, C.graph.Adj v w → ((C.cell v : Set Plane) ∩ (C.cell w : Set Plane)).Nonempty :=
  h.2.2.2.2

end GeneralGeometry

section Bridges

variable {V : Type*}

theorem IndexedCells.toCellConfiguration_graph (F : IndexedCells V) :
    F.toCellConfiguration.graph = F.graph.toSimpleGraph := rfl

theorem IndexedCells.hits_toCellConfiguration (F : IndexedCells V) (A : Set Plane) (v : V) :
    F.toCellConfiguration.Hits A v ↔ Hits F A v := Iff.rfl

theorem IndexedCells.inducedConnected_toCellConfiguration (F : IndexedCells V) (A : Set Plane) :
    F.toCellConfiguration.InducedConnected A ↔ SegmentReachable F A := Iff.rfl

theorem CellConfiguration.toCellConfiguration_toIndexedCells (C : CellConfiguration V)
    (h : C.LocallyFiniteGraph) : (C.toIndexedCells h).toCellConfiguration = C := rfl

theorem CellConfiguration.cellsOnly_cell (C : CellConfiguration V) :
    C.cellsOnly.cell = C.cell := rfl

end Bridges

end ReflectedGMS

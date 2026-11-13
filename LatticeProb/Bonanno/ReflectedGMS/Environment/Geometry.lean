/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.Geometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.PaperObjects
import LatticeProb.Bonanno.ReflectedWalk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
open MeasureTheory Set
namespace ReflectedGMS

abbrev Plane := BouRabeeGwynne.Euc 2

structure IndexedCells (V : Type*) where
  cell : V → TopologicalSpace.NonemptyCompacts Plane
  graph : ReflectedWalk.ConductanceGraph V

/-- The set of plane points covered by no cell. -/
def uncoveredSet {V : Type*} (F : IndexedCells V) : Set Plane :=
  (⋃ v, (F.cell v : Set Plane))ᶜ

/-- The geometric conditions on a cell configuration.

The fifth conjunct is the covering condition. It asks that the uncovered set be null for
**one-dimensional Hausdorff measure**, which covers both manuscripts at once:

* the earlier manuscript's Definition (`s:def:env`) assumes `⋃ H = ℂ`, so its uncovered set is
  empty and the clause holds trivially;
* the singular-set manuscript's Definition 1.1(ii) assumes `ℂ \ Ssing ⊆ ⋃ H` for a closed `Ssing`
  with `H¹(Ssing) = 0`, so the uncovered set is contained in `Ssing` and the clause follows by
  monotonicity of `μH[1]` (`ReflectedGMS.GeometrySingular`, `Environment/SingularGeometry.lean`).

`H¹`-nullity rather than Lebesgue-nullity is what the line arguments need: it makes the coordinate
projections of the uncovered set Lebesgue-null in `ℝ`, so almost every axis-parallel line misses the
uncovered set entirely. Lebesgue-nullity of a planar set does not imply that. -/
def Geometry {V : Type*} [Countable V] (F : IndexedCells V) : Prop :=
  (∀ v, IsConnected (F.cell v : Set Plane)) ∧
    (∀ v, (interior (F.cell v : Set Plane)).Nonempty) ∧
    (∀ v, volume (frontier (F.cell v : Set Plane)) = 0) ∧
    (∀ ⦃v w⦄, v ≠ w →
      Disjoint (interior (F.cell v : Set Plane)) (interior (F.cell w : Set Plane))) ∧
    μH[1] (uncoveredSet F) = 0 ∧
    F.graph.toSimpleGraph.Connected ∧
    (∀ v, (F.graph.toSimpleGraph.neighborSet v).Finite) ∧
    (∀ ⦃v w⦄, F.graph.toSimpleGraph.Adj v w →
      ((F.cell v : Set Plane) ∩ (F.cell w : Set Plane)).Nonempty)

def Hits {V : Type*} (F : IndexedCells V) (A : Set Plane) (v : V) : Prop :=
  ((F.cell v : Set Plane) ∩ A).Nonempty

def SegmentReachable {V : Type*} (F : IndexedCells V) (A : Set Plane) : Prop :=
  (F.graph.toSimpleGraph.induce {v | Hits F A v}).Preconnected

theorem segmentReachable_iff_finiteWalk {V : Type*} (F : IndexedCells V) (A : Set Plane) :
    SegmentReachable F A ↔
      ∀ v w, Hits F A v → Hits F A w →
        ∃ p : F.graph.toSimpleGraph.Walk v w,
          ∀ x ∈ p.support, Hits F A x := by
  constructor
  · intro h v w hv hw
    rcases h ⟨v, hv⟩ ⟨w, hw⟩ with ⟨q⟩
    have hs : ∀ x ∈ (q.map (SimpleGraph.Embedding.induce {v | Hits F A v}).toHom).support,
        Hits F A x := by
      intro x hx
      rw [SimpleGraph.Walk.support_map] at hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.property
    exact ⟨q.map (SimpleGraph.Embedding.induce {v | Hits F A v}).toHom, hs⟩
  · intro h v w
    rcases h v.1 w.1 v.2 w.2 with ⟨p, hp⟩
    exact ⟨by simpa using p.induce {x | Hits F A x} hp⟩

end ReflectedGMS

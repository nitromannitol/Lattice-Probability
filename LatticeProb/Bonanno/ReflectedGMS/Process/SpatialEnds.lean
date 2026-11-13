/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.SpatialEnds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Geometry
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs
import Mathlib.Topology.Order.Cadlag
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! Spatial predicates on mathlib's existing graph ends. No new end construction
or deterministic spatial image of an abstract end is introduced. -/
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal
namespace ReflectedGMS.SpatialEnds

variable {V : Type*}

/-- Reuse mathlib ends, sections of components outside all finite vertex sets. -/
abbrev GraphEnd (F : IndexedCells V) := F.graph.toSimpleGraph.end

/-- The actual component selected by an end outside a finite vertex set. -/
def endComponent (F : IndexedCells V) (e : GraphEnd F) (K : Finset V) : Set V :=
  (e.val (Opposite.op K)).supp

/-- Spatial escape along the directed family of finite graph complements.
This avoids choosing an exhaustion and asserts no deterministic image for
ends that fail to escape. -/
def AtSpatialInfinity (F : IndexedCells V) (e : GraphEnd F) : Prop :=
  ∀ R : ℝ, ∃ K : Finset V, ∀ L : Finset V, K ⊆ L →
    ∀ v ∈ endComponent F e L, ∀ z ∈ (F.cell v : Set Plane), R < ‖z‖

/-- Actual vertices and actual graph ends, retaining the end labels. -/
abbrev State (F : IndexedCells V) := V ⊕ GraphEnd F

/-- End labels are the actual components approached by the vertex path.
Every neighborhood is in the existing half-line topology, so this is two-sided
at positive times and one-sided at zero. No label may be chosen independently
of the neighboring vertex states. -/
def IsEndLabeling (F : IndexedCells V) (X : ℝ≥0 → State F) : Prop :=
  ∀ t e, X t = Sum.inr e → ∀ K : Finset V,
    ∀ᶠ s in 𝓝 t, ∀ v, X s = Sum.inl v → v ∈ endComponent F e K

/-- Collapse all end labels to the single nonvertex state of ReflectedWalk. -/
def collapse {F : IndexedCells V} : State F → Option V :=
  Sum.elim some (fun _ => none)

/-- A spatial extension agrees with all vertex positions and is continuous
at every end-valued time. Cadlag is mathlib's existing path predicate. -/
def IsSpatialExtension (F : IndexedCells V) (z : V → Plane)
    (X : ℝ≥0 → State F) (Z : ℝ≥0 → Plane) : Prop :=
  IsCadlag Z ∧
  (∀ t v, X t = Sum.inl v → Z t = z v) ∧
  (∀ t e, X t = Sum.inr e → ContinuousAt Z t)

def AvoidsSpatialInfinity (F : IndexedCells V) (X : ℝ≥0 → State F) : Prop :=
  ∀ t e, X t = Sum.inr e → ¬ AtSpatialInfinity F e

/-- A complete maximal holding interval at `v`, followed by the ordinary
edge jump to `w`. Maximality at the left endpoint prevents proper subintervals
from imposing inconsistent interpolation formulas. -/
def IsHoldingInterval (F : IndexedCells V) (X : ℝ≥0 → State F)
    (v w : V) (s t : ℝ≥0) : Prop :=
  s < t ∧
  (∀ r ∈ Ico s t, X r = Sum.inl v) ∧
  X t = Sum.inl w ∧ F.graph.toSimpleGraph.Adj v w ∧
  (s = 0 ∨ ∀ r < s, ∃ q ∈ Ioo r s, X q ≠ Sum.inl v)

/-- Every vertex-valued time belongs to a complete holding interval. This
retains the initial interval and does not posit a global enumeration of jumps. -/
def HasCompleteHoldingIntervals (F : IndexedCells V)
    (X : ℝ≥0 → State F) : Prop :=
  ∀ r v, X r = Sum.inl v →
    ∃ s t w, IsHoldingInterval F X v w s t ∧ r ∈ Ico s t

/-- Each nonzero spatial jump comes from one ordinary graph edge at the end
of its preceding holding interval; `leftLim` is mathlib's actual left limit. -/
def HasOnlyOrdinaryJumps (F : IndexedCells V) (z : V → Plane)
    (X : ℝ≥0 → State F) (Z : ℝ≥0 → Plane) : Prop :=
  ∀ t : ℝ≥0, 0 < t → Function.leftLim Z t ≠ Z t →
    ∃ s v w, IsHoldingInterval F X v w s t ∧
      Function.leftLim Z t = z v ∧ Z t = z w

/-- Continuous interpolation over the entire preceding holding interval,
using mathlib's affine line map. End-time values are the pathwise extension,
not a proposed deterministic spatial image of an abstract end. -/
def IsContinuousInterpolation (F : IndexedCells V) (z : V → Plane)
    (X : ℝ≥0 → State F) (Z Ztilde : ℝ≥0 → Plane) : Prop :=
  Continuous Ztilde ∧ HasCompleteHoldingIntervals F X ∧
  (∀ v w s t, IsHoldingInterval F X v w s t →
    ∀ r ∈ Icc s t, Ztilde r =
      AffineMap.lineMap (z v) (z w) (((r : ℝ) - s) / ((t : ℝ) - s))) ∧
  (∀ t e, X t = Sum.inr e → Ztilde t = Z t)

/-- Spatial boundedness on each compact time interval. -/
def LocallySpatiallyBounded (Z : ℝ≥0 → Plane) : Prop :=
  ∀ T : ℝ≥0, Bornology.IsBounded (Z '' Icc 0 T)

end ReflectedGMS.SpatialEnds

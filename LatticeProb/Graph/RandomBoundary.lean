import LatticeProb.Graph.Boundary
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of a random graph boundary

On a countable vertex set, coordinatewise measurable adjacency and membership
make the inner boundary a measurable set-valued map.
-/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb.Graph

/-- The inner boundary depends measurably on the graph and the vertex set. -/
theorem measurable_innerBoundary {Ω V : Type*} [MeasurableSpace Ω] [Countable V]
    (G : Ω → SimpleGraph V) (A : Ω → Set V)
    (hA : ∀ x, MeasurableSet {ω | x ∈ A ω})
    (hG : ∀ x y, MeasurableSet {ω | (G ω).Adj x y}) :
    Measurable fun ω => innerBoundary (G ω) (A ω) := by
  refine measurable_pi_iff.2 fun x => measurableSet_setOfPred.1 ?_
  change MeasurableSet {ω | x ∈ A ω ∧ ∃ y, y ∉ A ω ∧ (G ω).Adj x y}
  convert (hA x).inter (MeasurableSet.iUnion fun y => (hA y).compl.inter (hG x y)) using 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_compl_iff]

end LatticeProb.Graph

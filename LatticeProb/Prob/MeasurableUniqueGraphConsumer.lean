import LatticeProb.Prob.MeasurableUniqueGraph
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# A real square graph consumer

The graph relation `y = x²` has a measurable, everywhere unique fiber. The generic
unique-graph theorem produces a measurable function equal to squaring everywhere,
with distinct values at zero and one.
-/

namespace LatticeProb.Prob.MeasurableUniqueGraphConsumer

/-- The full real square graph is measurable in the product Borel space. -/
theorem measurableSet_square_graph :
    MeasurableSet {z : ℝ × ℝ | z.2 = z.1 ^ 2} :=
  measurableSet_eq_fun measurable_snd (measurable_fst.pow_const 2)

/-- Every vertical fiber of the real square graph contains exactly one point. -/
theorem square_graph_existsUnique (x : ℝ) :
    ∃! y : ℝ, (x, y) ∈ {z : ℝ × ℝ | z.2 = z.1 ^ 2} := by
  exact ⟨x ^ 2, rfl, fun _ hy => hy⟩

/-- Applying the generic unique-graph theorem to the real square relation gives an
actual measurable, nonconstant function with its full graph and point values. -/
theorem exists_measurable_square :
    ∃ f : ℝ → ℝ, Measurable f ∧
      (∀ x y, (x, y) ∈ {z : ℝ × ℝ | z.2 = z.1 ^ 2} ↔ f x = y) ∧
      (∀ x, f x = x ^ 2) ∧ f 0 = 0 ∧ f 1 = 1 ∧ f 0 ≠ f 1 := by
  obtain ⟨f, hf, hgraph⟩ := exists_measurable_of_unique_graph
    measurableSet_square_graph square_graph_existsUnique
  have heq : ∀ x, f x = x ^ 2 := fun x => (hgraph x (x ^ 2)).mp rfl
  have hzero : f 0 = 0 := by simpa only [zero_pow (by decide : 2 ≠ 0)] using heq 0
  have hone : f 1 = 1 := by simpa only [one_pow] using heq 1
  refine ⟨f, hf, hgraph, heq, hzero, hone, ?_⟩
  rw [hzero, hone]
  exact zero_ne_one

end LatticeProb.Prob.MeasurableUniqueGraphConsumer

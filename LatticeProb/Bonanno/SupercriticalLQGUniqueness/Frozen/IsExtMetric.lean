/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.IsExtMetric at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.ConstantSpeed
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Scratch freeze split of SLUMetric.lean:46. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- `d` is a metric on `α` which is allowed to take the value `∞` (DG l. 410–411, 429, 463):
it vanishes exactly on the diagonal, is symmetric, and satisfies the triangle inequality. -/
def IsExtMetric {α : Type*} (d : α × α → ℝ≥0∞) : Prop :=
  (∀ x, d (x, x) = 0) ∧
  (∀ x y, d (x, y) = 0 → x = y) ∧
  (∀ x y, d (x, y) = d (y, x)) ∧
  (∀ x y z, d (x, z) ≤ d (x, y) + d (y, z))
end SupercriticalLQGUniqueness

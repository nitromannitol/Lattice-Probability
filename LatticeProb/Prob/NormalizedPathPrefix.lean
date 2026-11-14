import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UnitInterval

/-! # Normalized finite prefixes of continuous paths -/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal unitInterval

namespace LatticeProb

/-- The prefix of a path of nonnegative duration, parametrized on the unit interval. -/
def normalizedPathPrefix {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (T : ℝ≥0) : C(unitInterval, E) where
  toFun u := w ⟨(u : ℝ) * (T : ℝ), mul_nonneg u.property.1 T.property⟩
  continuous_toFun := w.continuous.comp (by fun_prop)

@[simp] theorem normalizedPathPrefix_apply {E : Type*} [TopologicalSpace E]
    (w : C(ℝ≥0, E)) (T : ℝ≥0) (u : unitInterval) :
    normalizedPathPrefix w T u = w ⟨(u : ℝ) * (T : ℝ),
      mul_nonneg u.property.1 T.property⟩ := rfl

/-- Normalizing a finite prefix is jointly continuous in path and duration. -/
theorem continuous_normalizedPathPrefix {E : Type*} [TopologicalSpace E] :
    Continuous (fun p : C(ℝ≥0, E) × ℝ≥0 => normalizedPathPrefix p.1 p.2) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have ht : Continuous (fun p : (C(ℝ≥0, E) × ℝ≥0) × unitInterval =>
      (⟨(p.2 : ℝ) * (p.1.2 : ℝ), mul_nonneg p.2.property.1 p.1.2.property⟩ : ℝ≥0)) := by
    fun_prop
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk ht)

/-- With extended durations, normalization is measurable; infinity is totalized to zero. -/
theorem measurable_normalizedPathPrefix_toNNReal {E : Type*} [TopologicalSpace E]
    [MeasurableSpace C(ℝ≥0, E)] [BorelSpace C(ℝ≥0, E)]
    [MeasurableSpace C(unitInterval, E)] [BorelSpace C(unitInterval, E)] :
    Measurable (fun p : C(ℝ≥0, E) × ℝ≥0∞ => normalizedPathPrefix p.1 p.2.toNNReal) := by
  exact continuous_normalizedPathPrefix.measurable.comp
    (measurable_fst.prodMk (ENNReal.measurable_toNNReal.comp measurable_snd))

end LatticeProb

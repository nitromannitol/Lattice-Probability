import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Decomposition of measures with simple densities into level sets. -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace LatticeProb

/-- A measure with a simple density is the sum of the scaled restrictions to
its level sets. The base measure and the density may be infinite. -/
theorem withDensity_simpleFunc_eq_sum_restrict {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : SimpleFunc α ℝ≥0∞) :
    μ.withDensity f = ∑ c ∈ f.range, c • μ.restrict (f ⁻¹' {c}) := by
  classical
  ext s hs
  rw [withDensity_apply _ hs, f.lintegral_eq_lintegral (μ.restrict s)]
  simp only [SimpleFunc.lintegral, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply hs]
  congr 1
  ext c
  rw [Measure.restrict_apply (f.measurableSet_fiber c), inter_comm]

end LatticeProb

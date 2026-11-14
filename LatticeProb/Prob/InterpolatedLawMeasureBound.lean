import Mathlib
import LatticeProb.Prob.InterpolatedLaw

/-!
# Measure bounds for mixtures and interpolated laws

A mixture `∑' k, c k • Q k` of measures with weights summing to one gives a measurable set the
measure at most `a` as soon as every component with a nonzero weight does.  For the interpolated
law at `z` the components with a nonzero weight are those `k` with `dist(z, H k) < ε`.
-/

open MeasureTheory Filter Topology Set

open scoped ENNReal NNReal

namespace LatticeProb

section MixtureBound

variable {E : Type*} [MeasurableSpace E] {ι : Type*}

/-- A mixture with weights summing to one bounds the measure of a measurable set by `a` when every
component with a nonzero weight does. -/
theorem weightedMixture_apply_le {c : ι → ℝ≥0} (hc : HasSum c 1) (Q : ι → Measure E) {s : Set E}
    (hs : MeasurableSet s) {a : ℝ≥0∞} (h : ∀ k, c k ≠ 0 → Q k s ≤ a) :
    weightedMixture c Q s ≤ a := by
  rw [weightedMixture_apply c Q hs]
  have hsum : ∑' k, (c k : ℝ≥0∞) = 1 := by
    have h1 := ENNReal.coe_tsum hc.summable
    rw [hc.tsum_eq] at h1
    simpa using h1.symm
  calc ∑' k, (c k : ℝ≥0∞) * Q k s ≤ ∑' k, (c k : ℝ≥0∞) * a := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        by_cases hk : c k = 0
        · simp [hk]
        · exact mul_le_mul_right (h k hk) _
    _ = a := by rw [ENNReal.tsum_mul_right, hsum, one_mul]

end MixtureBound

section InterpBound

variable {Z : Type*} [PseudoMetricSpace Z] {ι : Type*} {E : Type*} [MeasurableSpace E]

/-- The interpolated law at `z` gives a measurable set the measure at most `a` when every `Q k` with
`dist(z, H k) < ε` does. -/
theorem interpLaw_apply_le {H : ι → Set Z} {ε : ℝ}
    (hloc : ∀ z, ∃ U ∈ 𝓝 z, {k | ∃ y ∈ U, interpWeight H ε k y ≠ 0}.Finite)
    (hpos : ∀ z, ∃ k, interpWeight H ε k z ≠ 0) (Q : ι → ProbabilityMeasure E) (z : Z)
    {s : Set E} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (h : ∀ k, Metric.infDist z (H k) < ε → (Q k : Measure E) s ≤ a) :
    (interpLaw H ε hloc hpos Q z : Measure E) s ≤ a := by
  unfold interpLaw
  rw [coe_weightedMixturePM]
  refine weightedMixture_apply_le (hasSum_normalizedWeight hloc hpos z) _ hs fun k hk => h k ?_
  rw [← interpWeight_ne_zero_iff]
  intro h0
  exact hk (by simp [normalizedWeight, h0])

end InterpBound

end LatticeProb

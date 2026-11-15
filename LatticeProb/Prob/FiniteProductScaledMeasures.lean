import Mathlib.MeasureTheory.Constructions.Pi

/-! Scaling finite products of finite measures. -/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb

/-- Scaling each factor of a finite product scales the product measure by the
product of the scalars. The identity includes zero scalars and empty products. -/
theorem pi_smul_finite {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, IsFiniteMeasure (μ i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  classical
  have (i : ι) : IsFiniteMeasure (c i • μ i) := (μ i).smul_finite (hc i)
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

end LatticeProb

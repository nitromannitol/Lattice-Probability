import LatticeProb.Prob.JumpChain.Uniformization
import LatticeProb.Prob.JumpChain.Generator
import LatticeProb.Prob.JumpChain.PoissonDerivative
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The generator of the uniformized transition kernel

A bounded observable is integrable against every transition row. Its expectation has
an exact Poisson series and a right derivative at zero equal to the jump generator.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Reorder the scalar factors of a weighted exponential-generating-series term. -/
theorem mul_div_mul_reorder (a b c d : ℝ) : a * b / c * d = a * (d / c * b) := by
  ring

/-- A bounded observable is integrable against any probability measure on the state space. -/
theorem integrable_of_abs_le (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) : Integrable f μ := by
  apply (integrable_const C).mono' (measurable_of_countable f).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun j ↦ by simpa only [Real.norm_eq_abs] using hf j

omit [Countable S] [MeasurableSingletonClass S] in
/-- The expectation of a bounded observable against a probability measure has the same bound. -/
theorem abs_integral_le (μ : Measure S) [IsProbabilityMeasure μ] (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) : |∫ j, f j ∂μ| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Filter.Eventually.of_forall fun j ↦ by simpa only [Real.norm_eq_abs] using hf j)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- The expectation of a bounded observable under the Poisson mixture is its exact series. -/
theorem integral_poissonKernel (κ : Kernel S S) [IsMarkovKernel κ] (r : ℝ≥0) (i : S)
    (f : S → ℝ) {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    (∫ j, f j ∂poissonKernel κ r i) =
      Real.exp (-(r : ℝ)) * ∑' n : ℕ,
        (∫ j, f j ∂(κ ^ n) i) / n.factorial * (r : ℝ) ^ n := by
  have hint := integrable_of_abs_le (poissonKernel κ r i) f hf
  rw [poissonKernel_eq_sum] at hint ⊢
  rw [integral_sum_measure hint]
  simp_rw [integral_smul_measure, smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hweight : 0 ≤ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial := by positivity
  rw [ENNReal.toReal_ofReal hweight]
  exact mul_div_mul_reorder _ _ _ _

namespace BoundedRates

/-- Uniformized expectations at nonnegative times have the exact exponential generating series. -/
theorem integral_transitionKernel (rates : BoundedRates S) (t : ℝ≥0) (i : S)
    (f : S → ℝ) {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    (∫ j, f j ∂rates.transitionKernel t i) =
      Real.exp (-(rates.R * t)) * ∑' n : ℕ,
        (∫ j, f j ∂(rates.kernel ^ n) i) / n.factorial * (rates.R * t) ^ n :=
  integral_poissonKernel rates.kernel _ i f hf

/-- The real singleton transition mass is the real Poisson uniformization series. -/
theorem transitionKernel_real_singleton (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    (rates.transitionKernel t i).real {j} =
      ∑' n : ℕ, Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial *
        ((rates.kernel ^ n) i).real {j} := by
  classical
  have hf (k : S) : |({j} : Set S).indicator (1 : S → ℝ) k| ≤ 1 := by
    by_cases hk : k ∈ ({j} : Set S)
    · simp only [Set.indicator_of_mem hk, Pi.one_apply, abs_one, le_refl]
    · simp only [Set.indicator_of_notMem hk, abs_zero, zero_le_one]
  have h := rates.integral_transitionKernel t i (({j} : Set S).indicator 1) hf
  simp_rw [integral_indicator_one (measurableSet_singleton j)] at h
  rw [← tsum_mul_left] at h
  exact h.trans (tsum_congr fun n ↦ (mul_div_mul_reorder _ _ _ _).symm)

/-- The real singleton transition probabilities sum to one. -/
theorem tsum_transitionKernel_real_singleton (rates : BoundedRates S) (t : ℝ≥0) (i : S) :
    (∑' j : S, (rates.transitionKernel t i).real {j}) = 1 := by
  have h := integral_countable (μ := rates.transitionKernel t i) (integrable_const (1 : ℝ))
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using h.symm

/-- The discrete kernel integrates bounded observables by the prescribed transition row. -/
theorem integral_kernel (rates : BoundedRates S) (i : S) (f : S → ℝ)
    {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    (∫ j, f j ∂rates.kernel i) = ∑' j, rates.p i j * f j := by
  rw [integral_countable (integrable_of_abs_le (rates.kernel i) f hf)]
  simp only [measureReal_def, rates.kernel_singleton,
    ENNReal.toReal_ofReal (rates.p_nonneg _ _), smul_eq_mul]

/-- The transition expectation has right derivative equal to the jump generator at zero. -/
theorem hasDerivWithinAt_integral_transitionKernel_zero (rates : BoundedRates S) (i : S)
    (f : S → ℝ) {C : ℝ} (hf : ∀ j, |f j| ≤ C) :
    HasDerivWithinAt (fun t : ℝ ↦
      ∫ j, f j ∂rates.transitionKernel (Real.toNNReal t) i)
      (∑' j, rates.q i j * (f j - f i)) (Ici 0) 0 := by
  let b : ℕ → ℝ := fun n ↦ ∫ j, f j ∂(rates.kernel ^ n) i
  have hb (n : ℕ) : |b n| ≤ C := abs_integral_le _ f hf
  have hpoisson : HasDerivAt (fun x : ℝ ↦ Real.exp (-x) *
      ∑' n : ℕ, b n / n.factorial * x ^ n) (b 1 - b 0) (rates.R * 0) := by
    simpa only [mul_zero] using hasDerivAt_poisson_average b hb
  have h := hpoisson.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul rates.R)
  have hbzero : b 0 = f i := by
    change (∫ j, f j ∂Kernel.id i) = f i
    exact integral_dirac f i
  have hbone : b 1 = ∑' j, rates.p i j * f j := by
    simpa only [b, pow_one] using rates.integral_kernel i f hf
  have hvalue : (b 1 - b 0) * rates.R =
      ∑' j, rates.q i j * (f j - f i) := by
    rw [hbone, hbzero, mul_comm]
    exact rates.uniformized_generator i f hf
  simp only [mul_one] at h
  rw [hvalue] at h
  apply h.hasDerivWithinAt.congr_of_mem _ (self_mem_Ici : (0 : ℝ) ∈ Ici 0)
  intro t ht
  rw [rates.integral_transitionKernel _ i f hf]
  simp only [Function.comp_apply, Real.coe_toNNReal t ht, b]

end BoundedRates

end

end LatticeProb.JumpChain

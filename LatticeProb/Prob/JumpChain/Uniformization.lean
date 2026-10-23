import LatticeProb.Prob.JumpChain.Rates
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Poisson mixtures of discrete transition kernels

The uniformized transition kernel is a Poisson mixture of the powers of the embedded
kernel. This module proves normalization and the semigroup law directly from Poisson
convolution. Identifying this kernel with the position process requires a separate
law of the exponential renewal count.
-/

namespace LatticeProb.JumpChain

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- A power of a Markov transition kernel is again a Markov transition kernel. -/
instance isMarkovKernel_pow (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [pow_succ]
    change IsMarkovKernel ((κ ^ n) ∘ₖ κ)
    infer_instance

/-- Mix the discrete transition powers with the Poisson distribution of parameter `r`. -/
def poissonKernel (κ : Kernel S S) (r : ℝ≥0) : Kernel S S :=
  Kernel.ofFunOfCountable fun i ↦ (poissonMeasure r).bind (fun n : ℕ ↦ (κ ^ n) i)

/-- Evaluate a Poisson mixture on a measurable set by integrating the discrete powers. -/
theorem poissonKernel_apply (κ : Kernel S S) (r : ℝ≥0) (i : S)
    {a : Set S} (ha : MeasurableSet a) :
    poissonKernel κ r i a = ∫⁻ n : ℕ, (κ ^ n) i a ∂poissonMeasure r := by
  exact Measure.bind_apply ha (measurable_of_countable _).aemeasurable

/-- Poisson mixing preserves total mass one. -/
instance isMarkovKernel_poissonKernel (κ : Kernel S S) [IsMarkovKernel κ] (r : ℝ≥0) :
    IsMarkovKernel (poissonKernel κ r) where
  isProbabilityMeasure i := by
    constructor
    rw [poissonKernel_apply κ r i MeasurableSet.univ]
    simp only [measure_univ, lintegral_const, mul_one]

/-- The exact nonnegative series defining a Poisson mixture. -/
theorem poissonKernel_apply_eq_tsum (κ : Kernel S S) (r : ℝ≥0) (i : S)
    {a : Set S} (ha : MeasurableSet a) :
    poissonKernel κ r i a =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) *
        (κ ^ n) i a := by
  rw [poissonKernel_apply κ r i ha, lintegral_countable']
  simp only [poissonMeasure_singleton, mul_comm]

/-- The Poisson mixture is a countable sum of scaled transition measures. -/
theorem poissonKernel_eq_sum (κ : Kernel S S) (r : ℝ≥0) (i : S) :
    poissonKernel κ r i = Measure.sum (fun n : ℕ ↦
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) • (κ ^ n) i) := by
  ext a ha
  rw [poissonKernel_apply_eq_tsum κ r i ha, Measure.sum_apply _ ha]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- Mixing at parameter zero leaves the starting state fixed. -/
theorem poissonKernel_zero (κ : Kernel S S) : poissonKernel κ 0 = Kernel.id := by
  ext i a ha
  rw [poissonKernel_apply_eq_tsum κ 0 i ha, tsum_eq_single 0]
  · simp only [NNReal.coe_zero, neg_zero, Real.exp_zero, pow_zero, one_mul,
      Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, pow_zero]
    rfl
  · intro n hn
    simp only [NNReal.coe_zero, zero_pow hn, mul_zero, zero_div, ENNReal.ofReal_zero,
      zero_mul]

/-- Two successive Poisson mixtures combine by addition of their parameters. -/
theorem poissonKernel_add (κ : Kernel S S) [IsMarkovKernel κ] (r u : ℝ≥0) :
    poissonKernel κ (r + u) = poissonKernel κ u ∘ₖ poissonKernel κ r := by
  ext i a ha
  rw [poissonKernel_apply κ (r + u) i ha, ← poissonMeasure_conv_poissonMeasure,
    Measure.lintegral_conv (measurable_of_countable _), Kernel.comp_apply' _ _ _ ha]
  change _ = ∫⁻ j, poissonKernel κ u j a
    ∂((poissonMeasure r).bind (fun n : ℕ ↦ (κ ^ n) i))
  rw [Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    ((Kernel.measurable_coe _ ha).aemeasurable)]
  apply lintegral_congr
  intro n
  simp_rw [poissonKernel_apply κ u _ ha]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro m
  exact Kernel.pow_add_apply_eq_lintegral κ n m i ha

namespace BoundedRates

/-- The transition kernel at time `t`, obtained by uniformization at the supplied rate. -/
def transitionKernel (rates : BoundedRates S) (t : ℝ≥0) : Kernel S S :=
  poissonKernel rates.kernel (⟨rates.R, rates.R_pos.le⟩ * t)

/-- Every uniformized transition row is a probability measure. -/
instance isMarkovKernel_transitionKernel (rates : BoundedRates S) (t : ℝ≥0) :
    IsMarkovKernel (rates.transitionKernel t) := by
  unfold transitionKernel
  infer_instance

/-- The uniformized singleton transition is exactly the Poisson series. -/
theorem transitionKernel_singleton (rates : BoundedRates S) (t : ℝ≥0) (i j : S) :
    rates.transitionKernel t i {j} =
      ∑' n : ℕ, ENNReal.ofReal
        (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) *
          (rates.kernel ^ n) i {j} :=
  poissonKernel_apply_eq_tsum rates.kernel _ i (measurableSet_singleton j)

/-- Transporting an initial measure through the kernel gives the exact initial-state mixture. -/
theorem transitionKernel_comp_singleton (rates : BoundedRates S) (μ : Measure S)
    (t : ℝ≥0) (j : S) :
    (rates.transitionKernel t ∘ₘ μ) {j} =
      ∑' i : S, μ {i} * ∑' n : ℕ, ENNReal.ofReal
        (Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial) *
          (rates.kernel ^ n) i {j} := by
  rw [Measure.bind_apply (measurableSet_singleton j) (Kernel.aemeasurable _),
    lintegral_countable']
  simp_rw [rates.transitionKernel_singleton]
  exact tsum_congr fun i ↦ mul_comm _ _

/-- At time zero the transition kernel is the identity. -/
theorem transitionKernel_zero (rates : BoundedRates S) :
    rates.transitionKernel 0 = Kernel.id := by
  simp only [transitionKernel, mul_zero, poissonKernel_zero]

/-- The uniformized kernels satisfy the Chapman--Kolmogorov semigroup identity. -/
theorem transitionKernel_add (rates : BoundedRates S) (s t : ℝ≥0) :
    rates.transitionKernel (s + t) = rates.transitionKernel t ∘ₖ rates.transitionKernel s := by
  unfold transitionKernel
  rw [mul_add, poissonKernel_add]

/-- Singleton transition masses sum to one on the countable state space. -/
theorem tsum_transitionKernel_singleton (rates : BoundedRates S) (t : ℝ≥0) (i : S) :
    ∑' j : S, rates.transitionKernel t i {j} = 1 := by
  have h := lintegral_countable' (μ := rates.transitionKernel t i) (fun _ ↦ 1)
  simpa only [lintegral_one, measure_univ, one_mul] using h.symm

/-- Chapman--Kolmogorov expressed as a countable sum of singleton probabilities. -/
theorem transitionKernel_add_singleton (rates : BoundedRates S) (s t : ℝ≥0) (i j : S) :
    rates.transitionKernel (s + t) i {j} =
      ∑' k : S, rates.transitionKernel s i {k} * rates.transitionKernel t k {j} := by
  rw [rates.transitionKernel_add, Kernel.comp_apply' _ _ _ (measurableSet_singleton j),
    lintegral_countable']
  exact tsum_congr fun k ↦ mul_comm _ _

end BoundedRates

end

end LatticeProb.JumpChain

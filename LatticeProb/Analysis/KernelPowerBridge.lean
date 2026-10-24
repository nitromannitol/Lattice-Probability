import LatticeProb.Analysis.KernelPowersCS
import LatticeProb.Graph.LongRangeKernel.WeightedGraph
import LatticeProb.Prob.JumpChain.Uniformization
import LatticeProb.Prob.JumpChain.Semigroup

/-!
# Bridges between density, matrix and measure kernel powers

Counting-measure densities agree with real stochastic matrix powers. Singleton masses of
uniformized kernel powers give the same entries, and hence the same Poisson series.
-/

namespace LatticeProb

open MeasureTheory ProbabilityTheory Graph.LongRangeKernel
open scoped NNReal

noncomputable section

/-- Stochastic matrix powers also satisfy the left-convolution recurrence. -/
lemma kernelPow_succ_left {X : Type*} {K : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, HasSum (K x) 1)
    (n : ℕ) (x y : X) :
    kernelPow K (n + 1) x y = ∑' z, K x z * kernelPow K n z y := by
  classical
  have hfirst : kernelPow K 1 = K := by
    funext u v
    simp [kernelPow, kernelComp, ite_mul]
  rw [Nat.add_comm n 1, kernelPow_add hK hrow, hfirst]

/-- Counting-measure density powers equal the nonnegative real stochastic matrix powers. -/
theorem densityPower_one_eq (X : Type*) [Countable X] (K : X → X → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (hrow : ∀ x, HasSum (K x) 1)
    (n : ℕ) (x y : X) :
    densityPower (fun _ => 1) (fun x y => ENNReal.ofReal (K x y)) n x y =
      ENNReal.ofReal (kernelPow K n x y) := by
  classical
  induction n generalizing x y with
  | zero =>
    by_cases h : x = y <;> simp [densityPower, identityDensity, kernelPow, h]
  | succ n ih =>
    have hs : Summable (fun z => K x z * kernelPow K n z y) := by
      apply (hrow x).summable.of_nonneg_of_le
        (fun z => mul_nonneg (hK x z) (kernelPow_nonneg hK n z y))
      intro z
      exact mul_le_of_le_one_right (hK x z)
        (kernel_entry_le_one (kernelPow_nonneg hK n) (kernelPow_hasSum hK hrow n) z y)
    simp only [densityPower, ih, ENNReal.coe_one, mul_one]
    rw [kernelPow_succ_left hK hrow, ENNReal.ofReal_tsum_of_nonneg
      (fun z => mul_nonneg (hK x z) (kernelPow_nonneg hK n z y)) hs]
    exact tsum_congr fun z => (ENNReal.ofReal_mul (hK x z)).symm

namespace JumpChain.BoundedRates

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- Singleton masses of uniformized kernel powers are real matrix power entries. -/
theorem kernel_pow_singleton (rates : JumpChain.BoundedRates S) (n : ℕ) (i j : S) :
    (rates.kernel ^ n) i {j} = ENNReal.ofReal (kernelPow rates.p n i j) := by
  classical
  induction n generalizing i j with
  | zero =>
    change Kernel.id i {j} = ENNReal.ofReal (kernelPow rates.p 0 i j)
    by_cases h : i = j <;> simp [kernelPow, h, Kernel.id_apply, Measure.dirac_apply']
  | succ n ih =>
    rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ (measurableSet_singleton j),
      lintegral_countable']
    simp only [rates.kernel_singleton, ih]
    change _ = ENNReal.ofReal (∑' z, kernelPow rates.p n i z * rates.p z j)
    have hs : Summable (fun z => kernelPow rates.p n i z * rates.p z j) := by
      apply (kernelPow_summable rates.p_nonneg rates.hasSum_p n i).of_nonneg_of_le
        (fun z => mul_nonneg (kernelPow_nonneg rates.p_nonneg n i z) (rates.p_nonneg z j))
      intro z
      exact mul_le_of_le_one_right (kernelPow_nonneg rates.p_nonneg n i z)
        (kernel_entry_le_one rates.p_nonneg rates.hasSum_p z j)
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun z => mul_nonneg (kernelPow_nonneg rates.p_nonneg n i z) (rates.p_nonneg z j)) hs]
    exact tsum_congr fun z => by
      rw [ENNReal.ofReal_mul (kernelPow_nonneg rates.p_nonneg n i z), mul_comm]

/-- The real transition mass is the Poisson series of real stochastic matrix powers. -/
theorem transitionKernel_real_singleton_eq_kernelPow (rates : JumpChain.BoundedRates S)
    (t : ℝ≥0) (i j : S) :
    (rates.transitionKernel t i).real {j} =
      ∑' n : ℕ, Real.exp (-(rates.R * t)) * (rates.R * t) ^ n / n.factorial *
        kernelPow rates.p n i j := by
  rw [rates.transitionKernel_real_singleton]
  apply tsum_congr
  intro n
  rw [Measure.real, rates.kernel_pow_singleton, ENNReal.toReal_ofReal
    (kernelPow_nonneg rates.p_nonneg n i j)]

end JumpChain.BoundedRates

end

end LatticeProb

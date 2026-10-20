/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/BinomialTail.lean.
-/
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hoeffding's lemma for a Bernoulli variable

This file proves `LatticeProb.bernoulli_hoeffding`: for `q ∈ [0, 1]` and `l : ℝ`,
`1 - q + q e^{-l} ≤ exp(-l q + l²/8)`. The proof applies Mathlib's Hoeffding lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` to `x ↦ x - q`
under the Bernoulli measure `bernoulliMeasure 1 0 q`.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace LatticeProb

/-- **Hoeffding's lemma for a Bernoulli variable**: for `q ∈ [0, 1]` and `l : ℝ`,
`1 - q + q * exp (-l) ≤ exp (-l * q + l ^ 2 / 8)`. It is derived from Mathlib's Hoeffding lemma
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, applied to `x ↦ x - q`
under `bernoulliMeasure 1 0 q`. -/
theorem bernoulli_hoeffding {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (l : ℝ) :
    1 - q + q * Real.exp (-l) ≤ Real.exp (-l * q + l ^ 2 / 8) := by
  set qI : I := ⟨q, hq0, hq1⟩
  have hb : ∀ᵐ x ∂(bernoulliMeasure (1 : ℝ) 0 qI), x - q ∈ Set.Icc (-q) (1 - q) := by
    rw [ae_iff]
    refine bernoulliMeasure_apply_of_notMem_of_notMem _
      ((measurableSet_Icc.preimage (measurable_id.sub_const q)).compl) ?_ ?_ <;>
      simp
  have hc : ∫ x, (x - q) ∂(bernoulliMeasure (1 : ℝ) 0 qI) = 0 := by
    rw [integral_bernoulliMeasure]; simp [qI]; ring
  have H := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := bernoulliMeasure (1 : ℝ) 0 qI)
    (X := fun x : ℝ => x - q) (by fun_prop) hb hc).mgf_le (-l)
  rw [mgf, integral_bernoulliMeasure] at H
  have hn : ((‖(1 - q) - -q‖₊ : NNReal) : ℝ) = 1 := by
    rw [coe_nnnorm, show (1 - q) - -q = 1 by ring]; simp
  simp only [qI, smul_eq_mul, NNReal.coe_pow, NNReal.coe_div, hn] at H
  have key : Real.exp (-l * q + l ^ 2 / 8) =
      Real.exp (-l * q) * Real.exp ((1 / 2) ^ 2 * (-l) ^ 2 / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [key]
  have hexp : 0 < Real.exp (-l * q) := Real.exp_pos _
  calc 1 - q + q * Real.exp (-l)
      = Real.exp (-l * q) * (q * Real.exp (-l * (1 - q)) + (1 - q) * Real.exp (-l * (0 - q))) := by
        rw [mul_add, ← mul_assoc, mul_comm (Real.exp _) q, mul_assoc, ← Real.exp_add,
          ← mul_assoc, mul_comm (Real.exp _) (1 - q), mul_assoc, ← Real.exp_add]
        ring_nf; rw [Real.exp_zero]; ring
    _ ≤ _ := by gcongr; simpa using H

namespace BernoulliHoeffdingExample

-- The inequality at `q = 1/2` and `l = 1`.
example : 1 - (1 / 2 : ℝ) + (1 / 2 : ℝ) * Real.exp (-1) ≤ Real.exp (-1 * (1 / 2 : ℝ) + 1 ^ 2 / 8) :=
  bernoulli_hoeffding (by norm_num) (by norm_num) 1

end BernoulliHoeffdingExample

end LatticeProb

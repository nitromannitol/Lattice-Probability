/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.BinomialTail at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Binomial lower-tail (Chernoff) bound and Hoeffding's lemma for a Bernoulli variable

* `LQGMetric.binomial_lower_tail` — **MQ Lemma 2.6 = LM Lemma 3.5**
  (Miller–Qian, *Geodesics in Brownian surfaces*, arXiv:1812.03913, Lemma 2.6;
  Gwynne–Miller, *Local metrics of the GFF*, arXiv:1905.00379, Lemma 3.5,
  `local-metrics-final.tex` lines 712–719): for `B_n ~ Bin(n, p)`, `p ∈ (0,1)`, `α ∈ (0,p)`,
  `P[B_n < α n] ≤ ((1-p)/(1-α))^n ((1-α)p/(α(1-p)))^{αn} = e^{-c_{p,α} n}`, with
  `c_{p,α} > 0` (`binomTailRate_pos`) and `c_{p,α} → ∞` as `p → 1` (`tendsto_binomTailRate`).
  Proof: the standard exponential Markov (Chernoff) bound with the optimal parameter
  `e^{-λ} = α(1-p)/((1-α)p)` (the proof MQ refer to; binomial theorem `add_pow`).
* `LQGMetric.bernoulli_hoeffding` — Hoeffding's lemma for a Bernoulli variable,
  `1 - q + q e^{-λ} ≤ exp(-λ q + λ²/8)`, obtained from mathlib's Hoeffding lemma
  `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` applied to `Ber(1,0,q)`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped unitInterval

namespace LQGMetric

/-- **Hoeffding's lemma for a Bernoulli variable**: for `q ∈ [0,1]` and `λ : ℝ`,
`1 - q + q e^{-λ} ≤ exp(-λ q + λ²/8)`. From mathlib's Hoeffding lemma
(`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) applied to `x ↦ x - q` under `Ber(1,0,q)`. -/
theorem bernoulli_hoeffding {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (l : ℝ) :
    1 - q + q * Real.exp (-l) ≤ Real.exp (-l * q + l ^ 2 / 8) := by
  set qI : I := ⟨q, hq0, hq1⟩
  have hb : ∀ᵐ x ∂(bernoulliMeasure (1 : ℝ) 0 qI), x - q ∈ Set.Icc (-q) (1 - q) := by
    rw [ae_iff]
    refine bernoulliMeasure_apply_of_notMem_of_notMem _
      ((measurableSet_Icc.preimage (measurable_id.sub_const q)).compl) ?_ ?_ <;>
      simp [hq0, hq1]
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

end LQGMetric

import LatticeProb.Prob.BernsteinFactorialMgf
import LatticeProb.Prob.BernsteinFactorialBound
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Tails under factorial moment budgets

Conditional factorial budgets imply a two-sided Bernstein tail and finite
absolute moments for sums of centered adapted increments.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- A factorial budget gives the two-sided Bernstein tail. -/
theorem abs_sum_tail_le_of_factorial_budget [IsProbabilityMeasure μ]
    {k : ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ} {a v s : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hs : 0 < s)
    (hmono : Monotone F) (hF : ∀ i, F i ≤ m₀)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hξint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hintq : ∀ i q : ℕ, Integrable (fun ω => |ξ i ω| ^ q) μ)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    (μ {ω | s ≤ |∑ i ∈ Finset.Icc 1 k, ξ i ω|}).toReal ≤
      2 * Real.exp (-(s ^ 2 / (2 * (v + a * s)))) := by
  have hden : 0 < v + a * s := by positivity
  have hlam : 0 ≤ s / (v + a * s) := (div_pos hs hden).le
  have hlam_a : (s / (v + a * s)) * a < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hden]
    nlinarith
  have hp := integrable_exp_sum_of_factorial_budget ha hlam hlam_a hmono hF hξ hξint
    hmean hintq hq
  have hn := integrable_exp_neg_sum_of_factorial_budget ha hlam hlam_a hmono hF hξ hξint
    hmean hintq hq
  apply mgf_abs_tail_le ha hv hs
  · simpa only [mgf] using hp.2
  · simpa only [mgf, mul_neg] using hn.2
  · exact hp.1
  · simpa only [mul_neg] using hn.1

/-- Sums satisfying a factorial budget have integrable absolute real powers. -/
theorem integrable_abs_sum_rpow_of_factorial_budget [IsProbabilityMeasure μ]
    {k : ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ} {a v r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hmono : Monotone F) (hF : ∀ i, F i ≤ m₀)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hξint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hintq : ∀ i q : ℕ, Integrable (fun ω => |ξ i ω| ^ q) μ)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    Integrable (fun ω => |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r) μ := by
  have ht : 0 < 1 / (2 * a) := by positivity
  have hta : (1 / (2 * a)) * a < 1 := by
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp
    norm_num
  have hp := (integrable_exp_sum_of_factorial_budget ha ht.le hta hmono hF hξ hξint
    hmean hintq hq).1
  have hn := (integrable_exp_neg_sum_of_factorial_budget ha ht.le hta hmono hF hξ hξint
    hmean hintq hq).1
  exact integrable_rpow_abs_of_integrable_exp_mul ht.ne' hp (by simpa only [neg_mul] using hn) hr

/-- A Bernstein tail and an integrable deterministic majorant make the
layer-cake integrand integrable. -/
theorem integrable_layerCake_of_bernstein_tail [IsProbabilityMeasure μ]
    {S : Ω → ℝ} {r a v : ℝ} (hr : 0 ≤ r)
    (htail : ∀ s : ℝ, 0 < s → (μ {ω | s ≤ |S ω|}).toReal ≤
      2 * Real.exp (-(s ^ 2 / (2 * (v + a * s)))))
    (htailint : Integrable (fun t : ℝ => r * t ^ (r - 1) *
      (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t))))))
      (volume.restrict (Set.Ioi 0))) :
    Integrable (fun t : ℝ => r * t ^ (r - 1) * (μ {ω | t ≤ |S ω|}).toReal)
      (volume.restrict (Set.Ioi 0)) := by
  have hant : Antitone (fun t : ℝ => (μ {ω | t ≤ |S ω|}).toReal) := by
    intro s t hst
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono
    intro ω hω
    exact hst.trans hω
  have hm : Measurable (fun t : ℝ => r * t ^ (r - 1) * (μ {ω | t ≤ |S ω|}).toReal) := by
    exact (measurable_const.mul (measurable_id.pow_const (r - 1))).mul hant.measurable
  apply Integrable.mono_nonneg htailint hm.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg hr (Real.rpow_nonneg (le_of_lt ht) _)) ENNReal.toReal_nonneg
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_left (htail t ht)
      (mul_nonneg hr (Real.rpow_nonneg (le_of_lt ht) _))

/-- The factorial moment conclusion follows from the deterministic tail
integrability estimate. -/
theorem moment_le_of_factorial_budget_of_tail_integrable [IsProbabilityMeasure μ]
    {k : ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ} {r a v : ℝ}
    (hr : 2 ≤ r) (ha : 0 < a) (hv : 0 < v)
    (hmono : Monotone F) (hF : ∀ i, F i ≤ m₀)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hξint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hintq : ∀ i q : ℕ, Integrable (fun ω => |ξ i ω| ^ q) μ)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)
    (htailint : Integrable (fun t : ℝ => r * t ^ (r - 1) *
      (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t))))))
      (volume.restrict (Set.Ioi 0))) :
    (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
      32 * (Real.sqrt (r * v) + r * a) := by
  have htail : ∀ s : ℝ, 0 < s →
      (μ {ω | s ≤ |∑ i ∈ Finset.Icc 1 k, ξ i ω|}).toReal ≤
        2 * Real.exp (-(s ^ 2 / (2 * (v + a * s)))) :=
    fun s hs => abs_sum_tail_le_of_factorial_budget ha hv hs hmono hF hξ hξint hmean hintq hq
  exact integral_rpow_le_of_tail hr ha hv (Eventually.of_forall fun ω => abs_nonneg _)
    (integrable_abs_sum_rpow_of_factorial_budget ha (by linarith) hmono hF hξ hξint hmean hintq hq)
    htail (integrable_layerCake_of_bernstein_tail (by linarith) htail htailint) htailint

end LatticeProb

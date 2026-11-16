import LatticeProb.Prob.BernsteinPredictableSupermartingale

/-!
# Moment-generating functions with predictable exponents

A deterministic bound on a sum of predictable exponents controls the
exponential moment of the corresponding sum of increments.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace LatticeProb

variable {Ω : Type*}

/-- A normalized exponential product is the exponential of a sum. -/
theorem normalizedExponentialProduct_eq_exp_sum (X H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    normalizedExponentialProduct (fun i ω => Real.exp (X i ω)) H n ω =
      Real.exp (∑ i ∈ Finset.range n, (X i ω - H i ω)) := by
  induction n with
  | zero => simp [normalizedExponentialProduct]
  | succ n ih =>
    rw [normalizedExponentialProduct]
    dsimp only
    rw [ih, Finset.sum_range_succ, Real.exp_add, sub_eq_add_neg, Real.exp_add]
    ring

/-- A deterministic budget on the predictable exponents bounds the exponential
moment of the sum and supplies its integrability. -/
theorem integrable_exp_sum_and_integral_le
    {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    {F : Filtration ℕ m₀} {X H : ℕ → Ω → ℝ} {k : ℕ} {B : ℝ}
    (hXmeas : ∀ n, n < k → Measurable[F (n + 1)] (X n))
    (hHmeas : ∀ n, n < k → Measurable[F n] (H n))
    (hXint : ∀ n, n < k → Integrable (fun ω => Real.exp (X n ω)) μ)
    (hXcond : ∀ n, n < k → μ[fun ω => Real.exp (X n ω) | F n] ≤ᵐ[μ]
      fun ω => Real.exp (H n ω))
    (hbudget : ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range k, H i ω ≤ B) :
    Integrable (fun ω => Real.exp (∑ i ∈ Finset.range k, X i ω)) μ ∧
      (∫ ω, Real.exp (∑ i ∈ Finset.range k, X i ω) ∂μ) ≤ Real.exp B := by
  let Y : ℕ → Ω → ℝ := fun i ω => Real.exp (X i ω)
  have hYm : ∀ n, n < k → Measurable[F (n + 1)] (Y n) :=
    fun n hn => (hXmeas n hn).exp
  have hY0 : ∀ n ω, 0 ≤ Y n ω := fun _ _ => (Real.exp_pos _).le
  have hz := normalizedExponentialProduct_step hYm hHmeas hY0 hXint hXcond
  have hzint := hz.2.1 k le_rfl
  have hzbound := integral_normalizedExponentialProduct_le_one hYm hHmeas hY0 hXint hXcond
  have hm : AEStronglyMeasurable (fun ω => Real.exp (∑ i ∈ Finset.range k, X i ω)) μ := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.exp
    apply Finset.measurable_sum
    intro i hi
    exact (hXmeas i (Finset.mem_range.mp hi)).mono (F.le (i + 1)) le_rfl
  have hle : ∀ᵐ ω ∂μ, Real.exp (∑ i ∈ Finset.range k, X i ω) ≤
      Real.exp B * normalizedExponentialProduct Y H k ω := by
    filter_upwards [hbudget] with ω hω
    rw [normalizedExponentialProduct_eq_exp_sum]
    have heq : (∑ i ∈ Finset.range k, X i ω) =
        (∑ i ∈ Finset.range k, (X i ω - H i ω)) + ∑ i ∈ Finset.range k, H i ω := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, Real.exp_add]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hω) (Real.exp_pos _).le).trans_eq
      (mul_comm _ _)
  have hint : Integrable (fun ω => Real.exp (∑ i ∈ Finset.range k, X i ω)) μ :=
    Integrable.mono_nonneg (hzint.const_mul _) hm
      (Eventually.of_forall fun ω => (Real.exp_pos _).le) hle
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, Real.exp (∑ i ∈ Finset.range k, X i ω) ∂μ) ≤
        ∫ ω, Real.exp B * normalizedExponentialProduct Y H k ω ∂μ :=
      integral_mono_ae hint (hzint.const_mul _) hle
    _ = Real.exp B * ∫ ω, normalizedExponentialProduct Y H k ω ∂μ := integral_const_mul _ _
    _ ≤ Real.exp B * 1 := mul_le_mul_of_nonneg_left hzbound (Real.exp_pos _).le
    _ = Real.exp B := mul_one _

end LatticeProb

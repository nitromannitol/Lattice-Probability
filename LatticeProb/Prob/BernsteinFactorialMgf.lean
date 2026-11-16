import LatticeProb.Prob.BernsteinPredictableMgf

/-!
# Exponential moments under factorial budgets

A conditional factorial-moment budget implies an exponential-moment bound for
the sum of centered adapted increments.
-/

open MeasureTheory ProbabilityTheory Filter Finset

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

private theorem sum_range_succ_eq_sum_Icc (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range k, f (i + 1) = ∑ i ∈ Finset.Icc 1 k, f i := by
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i _ j _ h
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨j - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · omega
  · intro i _; rfl

/-- The conditional factorial budget bounds the exponential moment of the
sum of centered adapted increments. -/
theorem integrable_exp_sum_of_factorial_budget [IsProbabilityMeasure μ]
    {k : ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ} {a v lam : ℝ}
    (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hmono : Monotone F) (hF : ∀ i, F i ≤ m₀)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hξint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hintq : ∀ i q : ℕ, Integrable (fun ω => |ξ i ω| ^ q) μ)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    Integrable (fun ω => Real.exp (lam * ∑ i ∈ Finset.Icc 1 k, ξ i ω)) μ ∧
      (∫ ω, Real.exp (lam * ∑ i ∈ Finset.Icc 1 k, ξ i ω) ∂μ) ≤
        Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
  let G : Filtration ℕ m₀ := ⟨F, hmono, hF⟩
  let X : ℕ → Ω → ℝ := fun n ω => lam * ξ (n + 1) ω
  let H : ℕ → Ω → ℝ := fun n => factorialPredictableExponent μ (F n) (ξ (n + 1)) lam
  have hm : ∀ n, n < k → Measurable[G (n + 1)] (X n) :=
    fun n _ => measurable_const.mul (hξ (n + 1))
  have hHm : ∀ n, n < k → Measurable[G n] (H n) :=
    fun n _ => measurable_factorialPredictableExponent (F n) (ξ (n + 1)) lam
  have hmem : ∀ n, n < k → n + 1 ∈ Finset.Icc 1 k := by
    intro n hn
    simp only [Finset.mem_Icc]
    omega
  have hpos : ∀ n, n < k → Integrable (fun ω => Real.exp (X n ω)) μ := by
    intro n hn
    have hξm : Measurable (ξ (n + 1)) := (hξ (n + 1)).mono (hF (n + 1)) le_rfl
    have habs := (integrable_exp_abs_of_factorial_moments ha hlam hlam_a hF hq (hmem n hn)
      hξm (hξint _) (fun q _ => hintq _ q)).1
    apply Integrable.mono_nonneg habs
      ((hm n hn).mono (hF (n + 1)) le_rfl).exp.aestronglyMeasurable
      (Eventually.of_forall fun ω => (Real.exp_pos _).le)
    exact Eventually.of_forall fun ω => Real.exp_le_exp.mpr (le_abs_self _)
  have hc : ∀ n, n < k → μ[fun ω => Real.exp (X n ω) | G n] ≤ᵐ[μ]
      fun ω => Real.exp (H n ω) := by
    intro n hn
    have hξm : Measurable (ξ (n + 1)) := (hξ (n + 1)).mono (hF (n + 1)) le_rfl
    have h := (condExp_exp_le_factorialPredictableExponent ha hlam hlam_a hF hq (hmem n hn)
      hξm (hmean (n + 1) (by omega) (by omega)) (hξint _)
      (fun q _ => hintq _ q)).1
    simpa only [Nat.add_sub_cancel] using h
  have hb : ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range k, H i ω ≤ lam ^ 2 * v / (2 * (1 - a * lam)) := by
    filter_upwards [sum_factorialPredictableExponent_le ha hlam hlam_a hq] with ω hω
    rw [← sum_range_succ_eq_sum_Icc] at hω
    simpa only [H, Nat.add_sub_cancel] using hω
  have h := integrable_exp_sum_and_integral_le hm hHm hpos hc hb
  have heq : (fun ω => ∑ i ∈ Finset.range k, X i ω) =
      fun ω => lam * ∑ i ∈ Finset.Icc 1 k, ξ i ω := by
    funext ω
    rw [Finset.mul_sum]
    exact sum_range_succ_eq_sum_Icc (fun i => lam * ξ i ω) k
  change Integrable (fun ω => Real.exp ((fun ω => ∑ i ∈ Finset.range k, X i ω) ω)) μ ∧
    (∫ ω, Real.exp ((fun ω => ∑ i ∈ Finset.range k, X i ω) ω) ∂μ) ≤ _ at h
  rw [heq] at h
  exact h

/-- The same factorial budget controls the exponential moment of the negated sum. -/
theorem integrable_exp_neg_sum_of_factorial_budget [IsProbabilityMeasure μ]
    {k : ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ} {a v lam : ℝ}
    (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hmono : Monotone F) (hF : ∀ i, F i ≤ m₀)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hξint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hintq : ∀ i q : ℕ, Integrable (fun ω => |ξ i ω| ^ q) μ)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    Integrable (fun ω => Real.exp (-(lam * ∑ i ∈ Finset.Icc 1 k, ξ i ω))) μ ∧
      (∫ ω, Real.exp (-(lam * ∑ i ∈ Finset.Icc 1 k, ξ i ω)) ∂μ) ≤
        Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
  have hm : ∀ i, 1 ≤ i → i ≤ k → μ[fun ω => -ξ i ω | F (i - 1)] =ᵐ[μ] 0 := by
    intro i hi hik
    filter_upwards [condExp_neg (μ := μ) (ξ i) (F (i - 1)), hmean i hi hik] with ω hneg hzero
    change (μ[-ξ i | F (i - 1)]) ω = 0
    rw [hneg]
    change -(μ[ξ i | F (i - 1)]) ω = 0
    rw [hzero]
    simp only [Pi.zero_apply, neg_zero]
  have hq' : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |(-ξ i ω')| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v := by
    simpa only [abs_neg] using hq
  have h := integrable_exp_sum_of_factorial_budget ha hlam hlam_a hmono hF
    (fun i => (hξ i).neg) (fun i => (hξint i).neg) hm
    (by simpa only [Pi.neg_apply, abs_neg] using hintq) hq'
  simpa only [Pi.neg_apply, Finset.sum_neg_distrib, mul_neg] using h

end LatticeProb

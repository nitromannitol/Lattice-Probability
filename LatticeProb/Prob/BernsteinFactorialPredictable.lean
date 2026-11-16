import LatticeProb.Prob.BernsteinFactorialCondExp

/-!
# Predictable factorial exponents

A measurable representative of the conditional absolute-moment series is
available for each increment.
-/

open MeasureTheory Filter Finset
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- A measurable representative of the conditional absolute-moment series. -/
noncomputable def factorialPredictableExponent (μ : @Measure Ω m₀)
    (m : MeasurableSpace Ω) (X : Ω → ℝ) (lam : ℝ) (ω : Ω) : ℝ :=
  (∑' q : ℕ, ENNReal.ofReal (if q < 2 then 0 else
    (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω)).toReal

/-- The exponent is measurable with respect to the conditioning sigma algebra. -/
theorem measurable_factorialPredictableExponent (m : MeasurableSpace Ω) (X : Ω → ℝ)
    (lam : ℝ) : Measurable[m] (factorialPredictableExponent μ m X lam) := by
  apply Measurable.ennreal_toReal
  apply Measurable.tsum
  intro q
  by_cases h : q < 2
  · simp only [h, ite_true]
    exact measurable_const
  · simp only [h, ite_false]
    exact ((stronglyMeasurable_condExp : StronglyMeasurable[m]
      (μ[fun ω' => |X ω'| ^ q | m])).measurable.const_mul _).ennreal_ofReal

/-- Under the factorial budget, the representative equals the conditional
absolute-moment series almost surely. -/
theorem factorialPredictableExponent_ae_eq [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)
    {j : ℕ} (hj : j ∈ s) :
    factorialPredictableExponent μ (F (j - 1)) (ξ j) lam =ᵐ[μ] fun ω =>
      ∑' q : ℕ, if q < 2 then 0 else
        (lam ^ q / (Nat.factorial q : ℝ)) *
          (μ[fun ω' => |ξ j ω'| ^ q | F (j - 1)]) ω := by
  have hnonneg : ∀ᵐ ω ∂μ, ∀ q : ℕ,
      0 ≤ (μ[fun ω' => |ξ j ω'| ^ q | F (j - 1)]) ω := by
    apply ae_all_iff.mpr
    intro q
    exact condExp_nonneg (Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) q)
  have hg := (summable_condExp_expMomentSeries ha hlam hlam_a hq).mono
    (fun _ h => h j hj)
  filter_upwards [hnonneg, hg] with ω hnonnegω hgω
  have ht : ∀ q : ℕ, 0 ≤ (if q < 2 then 0 else
      (lam ^ q / (Nat.factorial q : ℝ)) *
        (μ[fun ω' => |ξ j ω'| ^ q | F (j - 1)]) ω) := by
    intro q
    split_ifs
    · exact le_refl _
    · exact mul_nonneg (div_nonneg (pow_nonneg hlam q) (Nat.cast_nonneg _)) (hnonnegω q)
  change (∑' q : ℕ, ENNReal.ofReal (if q < 2 then 0 else
    (lam ^ q / (Nat.factorial q : ℝ)) *
      (μ[fun ω' => |ξ j ω'| ^ q | F (j - 1)]) ω)).toReal = _
  rw [← ENNReal.ofReal_tsum_of_nonneg ht hgω, ENNReal.toReal_ofReal (tsum_nonneg ht)]

/-- The predictable representative is nonnegative. -/
theorem factorialPredictableExponent_nonneg (m : MeasurableSpace Ω) (X : Ω → ℝ)
    (lam : ℝ) (ω : Ω) : 0 ≤ factorialPredictableExponent μ m X lam ω :=
  ENNReal.toReal_nonneg

/-- The total predictable exponent is bounded by the factorial budget. -/
theorem sum_factorialPredictableExponent_le [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    ∀ᵐ ω ∂μ, ∑ i ∈ s, factorialPredictableExponent μ (F (i - 1)) (ξ i) lam ω ≤
      lam ^ 2 * v / (2 * (1 - a * lam)) := by
  have heq : ∀ᵐ ω ∂μ, ∀ i ∈ s,
      factorialPredictableExponent μ (F (i - 1)) (ξ i) lam ω =
        ∑' q : ℕ, if q < 2 then 0 else
          (lam ^ q / (Nat.factorial q : ℝ)) *
            (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : i ∈ s
    · exact (factorialPredictableExponent_ae_eq ha hlam hlam_a hq hi).mono
        (fun _ h _ => h)
    · exact Eventually.of_forall fun _ h => (hi h).elim
  filter_upwards [heq, sum_condExp_expMomentSeries_le ha hlam hlam_a hq] with ω heqω hbω
  calc
    ∑ i ∈ s, factorialPredictableExponent μ (F (i - 1)) (ξ i) lam ω =
        ∑ i ∈ s, (∑' q : ℕ, if q < 2 then 0 else
          (lam ^ q / (Nat.factorial q : ℝ)) *
            (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω) :=
      Finset.sum_congr rfl (fun i hi => heqω i hi)
    _ ≤ _ := hbω

/-- Each signed conditional exponential is bounded by the predictable exponent. -/
theorem condExp_exp_le_factorialPredictableExponent [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hF : ∀ i, F i ≤ m₀)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)
    {j : ℕ} (hj : j ∈ s) (hξ : Measurable (ξ j))
    (hmean : μ[ξ j | F (j - 1)] =ᵐ[μ] 0)
    (hint1 : Integrable (ξ j) μ)
    (hintq : ∀ q : ℕ, 2 ≤ q → Integrable (fun ω => |ξ j ω| ^ q) μ) :
    (μ[fun ω => Real.exp (lam * ξ j ω) | F (j - 1)] ≤ᵐ[μ] fun ω =>
      Real.exp (factorialPredictableExponent μ (F (j - 1)) (ξ j) lam ω)) ∧
    (μ[fun ω => Real.exp (-(lam * ξ j ω)) | F (j - 1)] ≤ᵐ[μ] fun ω =>
      Real.exp (factorialPredictableExponent μ (F (j - 1)) (ξ j) lam ω)) := by
  have heq := factorialPredictableExponent_ae_eq ha hlam hlam_a hq hj
  constructor
  · filter_upwards [(condExp_exp_le_of_factorial_budget ha hlam hlam_a hF hq hj hξ
        hmean hint1 hintq).2, heq] with ω hb heqω
    simpa only [heqω] using hb
  · filter_upwards [condExp_exp_neg_le_of_factorial_budget ha hlam hlam_a hF hq hj hξ
        hmean hint1 hintq, heq] with ω hb heqω
    simpa only [heqω] using hb

end LatticeProb

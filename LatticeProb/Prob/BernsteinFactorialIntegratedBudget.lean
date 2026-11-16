import LatticeProb.Prob.BernsteinFactorialExpIntegrable

/-!
# Integrated factorial moment bounds

Conditional factorial moment bounds imply the corresponding unconditional
bounds for each increment.
-/

open MeasureTheory Filter Finset
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- A conditional factorial budget bounds each unconditional absolute moment. -/
theorem integral_abs_pow_le_of_condExp_budget [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v : ℝ} (hF : ∀ i, F i ≤ m₀)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)
    {j q : ℕ} (hj : j ∈ s) (hq2 : 2 ≤ q) :
    (∫ ω, |ξ j ω| ^ q ∂μ) ≤ (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v := by
  have hnn : ∀ᵐ ω ∂μ, ∀ i ∈ s,
      0 ≤ (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω := by
    have h : ∀ i : ℕ, ∀ᵐ ω ∂μ,
        0 ≤ (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω := fun i =>
      condExp_nonneg (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) q)
    filter_upwards [ae_all_iff.mpr h] with ω hω i _
    exact hω i
  have hbound := factorialMoment_term_le (B := fun q =>
    (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) (q := q) hnn (hq q hq2) hj
  have h := integral_mono_ae (integrable_condExp :
    Integrable (μ[fun ω' => |ξ j ω'| ^ q | F (j - 1)]) μ)
      (integrable_const ((Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)) hbound
  rw [integral_condExp (hF (j - 1))] at h
  simpa using h

/-- The integrated factorial series of an increment is summable under the
conditional moment budget. -/
theorem summable_integral_factorialSeries_of_condExp_budget [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hF : ∀ i, F i ≤ m₀)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)
    {j : ℕ} (hj : j ∈ s) :
    Summable (fun q : ℕ =>
      ∫ ω, ‖(lam * ξ j ω) ^ q / (Nat.factorial q : ℝ)‖ ∂μ) := by
  have hnn : ∀ q : ℕ, 0 ≤ ∫ ω, |ξ j ω| ^ q ∂μ :=
    fun q => integral_nonneg fun ω => pow_nonneg (abs_nonneg _) q
  have hb : ∀ q : ℕ, 2 ≤ q → (∫ ω, |ξ j ω| ^ q ∂μ) ≤
      (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v :=
    fun q hq2 => integral_abs_pow_le_of_condExp_budget hF hq hj hq2
  have hg := summable_expMomentSeries ha hlam hlam_a hnn hb
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 2] with q hq2
  rw [ite_eq_right (by omega : ¬ q < 2), Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
  have heq : (fun ω => ‖(lam * ξ j ω) ^ q / (Nat.factorial q : ℝ)‖) =
      fun ω => (lam ^ q / (Nat.factorial q : ℝ)) * |ξ j ω| ^ q := by
    funext ω
    simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, abs_of_nonneg hlam,
      Nat.abs_cast]
    ring
  rw [heq, integral_const_mul]

/-- The conditional factorial budget and integrability of the factorial terms
imply integrability of the absolute exponential of each increment. -/
theorem integrable_exp_abs_of_condExp_budget [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hF : ∀ i, F i ≤ m₀)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)
    {j : ℕ} (hj : j ∈ s) (hξ : Measurable (ξ j))
    (hint : ∀ q : ℕ,
      Integrable (fun ω => (lam * ξ j ω) ^ q / (Nat.factorial q : ℝ)) μ) :
    Integrable (fun ω => Real.exp |lam * ξ j ω|) μ ∧
      (∑' q : ℕ, ∫⁻ ω,
        ‖(lam * ξ j ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ) ≠ ∞ :=
  integrable_exp_abs_of_summable_factorial_integrals hξ hint
    (summable_integral_factorialSeries_of_condExp_budget ha hlam hlam_a hF hq hj)

/-- Integrable absolute moments supply the factorial-series term hypotheses. -/
theorem integrable_factorialSeries_term {X : Ω → ℝ} {lam : ℝ}
    (hlam : 0 ≤ lam) (hX : Measurable X)
    (hint : ∀ q : ℕ, Integrable (fun ω => |X ω| ^ q) μ) (q : ℕ) :
    Integrable (fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ)) μ := by
  apply (integrable_norm_iff (by fun_prop : AEStronglyMeasurable
    (fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ)) μ)).mp
  have heq : (fun ω => ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖) =
      fun ω => (lam ^ q / (Nat.factorial q : ℝ)) * |X ω| ^ q := by
    funext ω
    simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, abs_of_nonneg hlam,
      Nat.abs_cast]
    ring
  rw [heq]
  exact (hint q).const_mul _

/-- The conditional factorial budget and integrability of the increment and
its higher absolute moments imply exponential integrability. -/
theorem integrable_exp_abs_of_factorial_moments [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hF : ∀ i, F i ≤ m₀)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v)
    {j : ℕ} (hj : j ∈ s) (hξ : Measurable (ξ j))
    (hint1 : Integrable (ξ j) μ)
    (hintq : ∀ q : ℕ, 2 ≤ q → Integrable (fun ω => |ξ j ω| ^ q) μ) :
    Integrable (fun ω => Real.exp |lam * ξ j ω|) μ ∧
      (∑' q : ℕ, ∫⁻ ω,
        ‖(lam * ξ j ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ) ≠ ∞ := by
  have h : ∀ q : ℕ, Integrable (fun ω => |ξ j ω| ^ q) μ := by
    intro q
    rcases q with _ | _ | q
    · simp
    · simpa using hint1.abs
    · exact hintq _ (by omega)
  exact integrable_exp_abs_of_condExp_budget ha hlam hlam_a hF hq hj hξ
    (integrable_factorialSeries_term hlam hξ h)

end LatticeProb

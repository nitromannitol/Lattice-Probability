import LatticeProb.Prob.BernsteinFactorialIntegratedBudget
import LatticeProb.Prob.BernsteinFactorialSummability

/-!
# Conditional exponential moments from factorial budgets

A conditional factorial moment budget controls the exponential moment of each
centered increment by its predictable absolute-moment series.
-/

open MeasureTheory Filter Finset
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- A centered increment satisfies the conditional exponential estimate under a
conditional factorial moment budget. -/
theorem condExp_exp_le_of_factorial_budget [IsProbabilityMeasure μ]
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
    Integrable (fun ω => Real.exp |lam * ξ j ω|) μ ∧
      μ[fun ω => Real.exp (lam * ξ j ω) | F (j - 1)] ≤ᵐ[μ] fun ω =>
        Real.exp (∑' q : ℕ, if q < 2 then 0 else
          (lam ^ q / (Nat.factorial q : ℝ)) *
            (μ[fun ω' => |ξ j ω'| ^ q | F (j - 1)]) ω) := by
  have hint : ∀ q : ℕ, Integrable (fun ω => |ξ j ω| ^ q) μ := by
    intro q
    rcases q with _ | _ | q
    · simp
    · simpa using hint1.abs
    · exact hintq _ (by omega)
  have hseries := integrable_exp_abs_of_factorial_moments ha hlam hlam_a hF hq hj hξ hint1 hintq
  have hg := (summable_condExp_expMomentSeries ha hlam hlam_a hq).mono
    (fun _ h => h j hj)
  refine ⟨hseries.1, condExp_exp_le_of_momentSeries (hF (j - 1)) hlam hξ hmean
    (integrable_factorialSeries_term hlam hξ hint) ?_ (summable_condExp_factorialSeries hlam hg)
      hg hseries.2⟩
  intro q
  exact (hint q).const_mul _

/-- The same conditional exponential estimate holds for the negated increment. -/
theorem condExp_exp_neg_le_of_factorial_budget [IsProbabilityMeasure μ]
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
    μ[fun ω => Real.exp (-(lam * ξ j ω)) | F (j - 1)] ≤ᵐ[μ] fun ω =>
      Real.exp (∑' q : ℕ, if q < 2 then 0 else
        (lam ^ q / (Nat.factorial q : ℝ)) *
          (μ[fun ω' => |ξ j ω'| ^ q | F (j - 1)]) ω) := by
  have hq' : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |(-ξ i ω')| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v := by
    simpa only [abs_neg] using hq
  have hm : μ[fun ω => -ξ j ω | F (j - 1)] =ᵐ[μ] 0 := by
    filter_upwards [condExp_neg (μ := μ) (ξ j) (F (j - 1)), hmean] with ω hneg hzero
    change (μ[-ξ j | F (j - 1)]) ω = 0
    rw [hneg]
    change -(μ[ξ j | F (j - 1)]) ω = 0
    rw [hzero]
    simp only [Pi.zero_apply, neg_zero]
  have h := condExp_exp_le_of_factorial_budget ha hlam hlam_a hF hq' hj hξ.neg hm
    hint1.neg (by simpa only [abs_neg] using hintq)
  simpa only [abs_neg, mul_neg] using h.2

end LatticeProb

import LatticeProb.Prob.BernsteinFactorialTail
import LatticeProb.Prob.BernsteinTailIntegrable
import LatticeProb.Prob.BernsteinMoment

/-!
# Bernstein moment estimates

Bounded martingale differences and factorial moment budgets admit a common
moment constant.
-/

open MeasureTheory

namespace LatticeProb

/-- A factorial moment budget implies a Bernstein moment estimate. -/
theorem moment_le_of_factorial_budget
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : @Measure Ω m} [IsProbabilityMeasure μ]
    {k : ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ} {r a v : ℝ}
    (hr : 2 ≤ r) (ha : 0 < a) (hv : 0 < v)
    (hmono : Monotone F) (hF : ∀ i, F i ≤ m)
    (hξ : ∀ i, Measurable[F i] (ξ i)) (hξint : ∀ i, Integrable (ξ i) μ)
    (hmean : ∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0)
    (hintq : ∀ i q : ℕ, Integrable (fun ω => |ξ i ω| ^ q) μ)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
      32 * (Real.sqrt (r * v) + r * a) := by
  exact moment_le_of_factorial_budget_of_tail_integrable hr ha hv hmono hF hξ hξint
    hmean hintq hq (integrable_rpow_mul_bernstein_tail r a v hr ha hv)

/-- Both Bernstein moment estimates hold with the same universal constant. -/
theorem bernstein_moment_estimates :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : @Measure Ω m) (_ : IsProbabilityMeasure μ)
        (k : ℕ) (F : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ) (r a : ℝ),
        Monotone F → (∀ i, F i ≤ m) →
        (∀ i, Measurable[F i] (ξ i)) → (∀ i, Integrable (ξ i) μ) →
        (∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0) →
        2 ≤ r → 0 < a →
        ((∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) →
          (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
            C * (Real.sqrt r *
              (∫ ω, (∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂μ)
                ^ (1 / r) + r * a)) ∧
        (∀ v : ℝ, 0 < v → (∀ (i : ℕ) (q : ℕ), Integrable (fun ω => |ξ i ω| ^ q) μ) →
          (∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
            ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
              (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) →
          (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
            C * (Real.sqrt (r * v) + r * a)) := by
  refine ⟨32, by norm_num, ?_⟩
  intro Ω m μ hμ k F ξ r a hmono hF hξ hξint hmean hr ha
  let : IsProbabilityMeasure μ := hμ
  constructor
  · intro hbound
    exact boundedDifference_moment32_source Ω m μ k F ξ r a hmono hF hξ hξint hmean hr ha hbound
  · intro v hv hintq hq
    exact moment_le_of_factorial_budget hr ha hv hmono hF hξ hξint hmean hintq hq

end LatticeProb

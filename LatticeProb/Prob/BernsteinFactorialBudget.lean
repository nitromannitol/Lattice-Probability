import LatticeProb.Prob.BernsteinFactorialProducerThree

/-!
# Conditional factorial moment budgets

A bound on the sum of conditional moments bounds the sum of the corresponding
predictable exponential-series terms simultaneously almost everywhere.
-/

open MeasureTheory Filter Finset

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- The total conditional factorial moment budget controls the sum of the
predictable exponential-series terms. -/
theorem sum_condExp_expMomentSeries_le [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (∑' q : ℕ, if q < 2 then 0 else
        (lam ^ q / (Nat.factorial q : ℝ)) *
          (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω) ≤
        lam ^ 2 * v / (2 * (1 - a * lam)) := by
  have hnn : ∀ᵐ ω ∂μ, ∀ i q : ℕ,
      0 ≤ (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro q
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) q)
  have hq' : ∀ᵐ ω ∂μ, ∀ q : ℕ, 2 ≤ q →
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v := by
    apply ae_all_iff.mpr
    intro q
    by_cases h : 2 ≤ q
    · exact (hq q h).mono fun _ hω _ => hω
    · exact Filter.Eventually.of_forall fun _ h' => (h h').elim
  filter_upwards [hnn, hq'] with ω hnnω hqω
  exact sum_expMomentSeries_le ha hlam hlam_a (fun i _ q => hnnω i q) hqω


/-- Each predictable exponential-series term is summable under a total
conditional factorial moment budget. -/
theorem summable_condExp_expMomentSeries [IsProbabilityMeasure μ]
    {s : Finset ℕ} {F : ℕ → MeasurableSpace Ω} {ξ : ℕ → Ω → ℝ}
    {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1)
    (hq : ∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) :
    ∀ᵐ ω ∂μ, ∀ i ∈ s, Summable (fun q : ℕ => if q < 2 then 0 else
      (lam ^ q / (Nat.factorial q : ℝ)) *
        (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω) := by
  have hnn : ∀ᵐ ω ∂μ, ∀ i q : ℕ,
      0 ≤ (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro q
    exact condExp_nonneg (Filter.Eventually.of_forall fun ω => pow_nonneg (abs_nonneg _) q)
  have hq' : ∀ᵐ ω ∂μ, ∀ q : ℕ, 2 ≤ q →
      ∑ i ∈ s, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω ≤
        (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v := by
    apply ae_all_iff.mpr
    intro q
    by_cases h : 2 ≤ q
    · exact (hq q h).mono fun _ hω _ => hω
    · exact Filter.Eventually.of_forall fun _ h' => (h h').elim
  filter_upwards [hnn, hq'] with ω hnnω hqω
  intro i hi
  apply summable_expMomentSeries ha hlam hlam_a (hnnω i)
  intro q hq2
  exact (Finset.single_le_sum (fun j _ => hnnω j q) hi).trans (hqω q hq2)

end LatticeProb

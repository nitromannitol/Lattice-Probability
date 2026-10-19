import LatticeProb.Prob.McLeish.Truncation
import LatticeProb.Prob.McLeish.ProductMoment
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Basic

/-!
# The predictably truncated array satisfies the product-moment hypotheses

For a real array `X 0, X 1, …` whose partial sums form a martingale, the predictable truncation
`trunc X c` keeps the term `X k` only while the squares of the earlier terms sum to at most `c`.
This file records the measurability of the increments, of the sums of squares and of the
truncated terms, together with the bounds on the product `∏ (1 + i t Y k)` built from the
truncated array. These are exactly the hypotheses needed to apply the product-moment results to
`trunc X c`: the product has expectation one and finite second moment.
-/

namespace LatticeProb.McLeish

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The terms of a martingale of partial sums are strongly measurable one step ahead. -/
theorem stronglyMeasurable_increment {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (X k) := by
  have hdiff : X k = (fun ω => ∑ j ∈ Finset.range (k + 1), X j ω) -
      fun ω => ∑ j ∈ Finset.range k, X j ω := by
    funext ω
    simp [Finset.sum_range_succ]
  rw [hdiff]
  exact (hX.1 (k + 1)).sub ((hX.1 k).mono (ℱ.mono (Nat.le_succ k)))

/-- The sum of the squares of the first `k` terms is measurable at time `k`. -/
theorem stronglyMeasurable_sqSum {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (k : ℕ) :
    StronglyMeasurable[ℱ k] (sqSum X k) := by
  unfold sqSum
  convert Finset.stronglyMeasurable_sum (Finset.range k) fun j hj =>
    ((stronglyMeasurable_increment hX j).mono
      (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))).pow 2 using 1
  funext ω
  simp [Finset.sum_apply]

/-- The predictably truncated term is strongly measurable one step ahead. -/
theorem stronglyMeasurable_trunc {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c : ℝ) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (trunc X c k) := by
  have hset : MeasurableSet[ℱ k] {ω | sqSum X k ω ≤ c} :=
    (stronglyMeasurable_sqSum hX k).measurable measurableSet_Iic
  have hset' : MeasurableSet[ℱ (k + 1)] {ω | sqSum X k ω ≤ c} :=
    ℱ.mono (Nat.le_succ k) _ hset
  have heq : trunc X c k = {ω | sqSum X k ω ≤ c}.indicator (X k) := by
    funext ω
    by_cases h : sqSum X k ω ≤ c <;> simp [trunc, h]
  rw [heq]
  exact (stronglyMeasurable_increment hX k).indicator hset'

/-- On the event that the squares of the first `k` terms sum to at most `c`, the product
`∏ (1 + i t Y k)` built from the truncated array has modulus at most `exp (t ^ 2 c / 2)`. -/
theorem norm_prodOneAddI_trunc_le (X : ℕ → Ω → ℝ) (c t : ℝ) (k : ℕ) (ω : Ω) (h : sqSum X k ω ≤ c) :
    ‖prodOneAddI (trunc X c) t k ω‖ ≤ Real.exp (t ^ 2 * c / 2) := by
  have h1 : ‖prodOneAddI (trunc X c) t k ω‖ ^ 2 ≤ Real.exp (t ^ 2 * c) := by
    refine (norm_prodOneAddI_sq_le_exp (trunc X c) t k ω).trans (Real.exp_le_exp.2 ?_)
    exact mul_le_mul_of_nonneg_left ((sqSum_trunc_le X c k ω).trans h) (sq_nonneg t)
  have hB : Real.exp (t ^ 2 * c / 2) * Real.exp (t ^ 2 * c / 2) = Real.exp (t ^ 2 * c) := by
    rw [← Real.exp_add, add_halves]
  have hB0 : 0 ≤ Real.exp (t ^ 2 * c / 2) := (Real.exp_pos _).le
  nlinarith [norm_nonneg (prodOneAddI (trunc X c) t k ω)]

/-- The squared modulus of the product built from the truncated array is at most
`exp (t ^ 2 c) (1 + t ^ 2 M)` whenever every term of the original array up to time `n` has square
at most `M`. -/
theorem norm_prodOneAddI_trunc_sq_le (X : ℕ → Ω → ℝ) (c t M : ℝ) (n : ℕ) (ω : Ω) (hc0 : 0 ≤ c)
    (hM0 : 0 ≤ M) (hM : ∀ k < n, X k ω ^ 2 ≤ M) :
    ‖prodOneAddI (trunc X c) t n ω‖ ^ 2 ≤ Real.exp (t ^ 2 * c) * (1 + t ^ 2 * M) := by
  have hc : ∀ k < n, trunc X c k ω ≠ 0 → ∑ j ∈ Finset.range k, trunc X c j ω ^ 2 ≤ c := by
    intro k _ hne
    have hsk : sqSum X k ω ≤ c := by
      by_contra hcon
      exact hne (by simp [trunc, hcon])
    exact (sqSum_trunc_le X c k ω).trans hsk
  have hM' : ∀ k < n, trunc X c k ω ^ 2 ≤ M := by
    intro k hk
    unfold trunc
    split_ifs
    · exact hM k hk
    · simpa using hM0
  exact norm_prodOneAddI_sq_le (trunc X c) t c M n ω hc0 hM0 hc hM'

/-- The product built from the predictably truncated array has expectation one. -/
theorem integral_prodOneAddI_trunc {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c t : ℝ) (n : ℕ) :
    ∫ ω, prodOneAddI (trunc X c) t n ω ∂P = 1 := by
  refine integral_prodOneAddI (martingale_trunc hX c) t (Real.exp (t ^ 2 * c / 2))
    (fun k => {ω | sqSum X k ω ≤ c}) (fun k => ?_) (fun k ω hω => ?_) (fun k ω hω => ?_) n
  · exact (stronglyMeasurable_sqSum hX k).measurable measurableSet_Iic
  · have hnot : ¬ sqSum X k ω ≤ c := hω
    simp [trunc, hnot]
  · exact norm_prodOneAddI_trunc_le X c t k ω hω

/-- The product built from the predictably truncated array is square integrable, and its second
moment is at most `exp (t ^ 2 c) (1 + t ^ 2 ∫ M)` for any integrable majorant `M` of the squares
of the original array. -/
theorem memLp_prodOneAddI_trunc {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c t : ℝ) (hc0 : 0 ≤ c) (n : ℕ)
    (M : Ω → ℝ) (hMint : Integrable M P) (hM0 : ∀ ω, 0 ≤ M ω)
    (hM : ∀ ω, ∀ k < n, X k ω ^ 2 ≤ M ω) :
    MemLp (prodOneAddI (trunc X c) t n) 2 P ∧
      ∫ ω, ‖prodOneAddI (trunc X c) t n ω‖ ^ 2 ∂P ≤
        Real.exp (t ^ 2 * c) * (1 + t ^ 2 * ∫ ω, M ω ∂P) := by
  have hFsm : StronglyMeasurable[mΩ] (prodOneAddI (trunc X c) t n) :=
    (stronglyMeasurable_prodOneAddI (stronglyMeasurable_trunc hX c) t n).mono (ℱ.le n)
  have hFaesm : AEStronglyMeasurable (prodOneAddI (trunc X c) t n) P := hFsm.aestronglyMeasurable
  have hsqaesm : AEStronglyMeasurable (fun ω => ‖prodOneAddI (trunc X c) t n ω‖ ^ 2) P :=
    (hFsm.norm.pow 2).aestronglyMeasurable
  have hg : Integrable (fun ω => Real.exp (t ^ 2 * c) * (1 + t ^ 2 * M ω)) P :=
    ((integrable_const (1 : ℝ)).add (hMint.const_mul (t ^ 2))).const_mul _
  have hle : ∀ ω, ‖prodOneAddI (trunc X c) t n ω‖ ^ 2 ≤
      Real.exp (t ^ 2 * c) * (1 + t ^ 2 * M ω) :=
    fun ω => norm_prodOneAddI_trunc_sq_le X c t (M ω) n ω hc0 (hM0 ω) (hM ω)
  have hsqint : Integrable (fun ω => ‖prodOneAddI (trunc X c) t n ω‖ ^ 2) P :=
    hg.mono' hsqaesm (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hle ω)
  have hmean : ∫ ω, Real.exp (t ^ 2 * c) * (1 + t ^ 2 * M ω) ∂P =
      Real.exp (t ^ 2 * c) * (1 + t ^ 2 * ∫ ω, M ω ∂P) := by
    rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) (hMint.const_mul (t ^ 2)),
      integral_const_mul]
    simp
  refine ⟨(memLp_two_iff_integrable_sq_norm hFaesm).2 hsqint, ?_⟩
  rw [← hmean]
  exact integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) hg (ae_of_all _ hle)

end LatticeProb.McLeish

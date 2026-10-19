import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Probability.Martingale.Basic

/-!
# Predictable truncation of a martingale difference array

For a sequence `X 0, X 1, …` of real random variables, the term `X k` is kept only while the
squares of the earlier terms sum to at most a level `c`; otherwise it is replaced by zero.
When the partial sums of `X` form a martingale, so do the partial sums of the truncated terms.
The sum of the squares of the truncated terms never exceeds the sum of the squares of the
original terms.
-/

namespace LatticeProb.McLeish

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The sum of the squares of the first `k` terms. -/
def sqSum (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.range k, X j ω ^ 2

/-- The predictable truncation: the term `k` is kept while the earlier squares sum to at most `c`. -/
noncomputable def trunc (X : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if sqSum X k ω ≤ c then X k ω else 0

/-- The sums of squares of the first terms are nondecreasing in the number of terms. -/
private lemma sqSum_mono (X : ℕ → Ω → ℝ) (ω : Ω) {j k : ℕ} (hjk : j ≤ k) :
    sqSum X j ω ≤ sqSum X k ω :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hjk) fun _ _ _ => sq_nonneg _

/-- A term with index at most `k` is kept whenever the squares of the first `k` terms sum to at
most `c`. -/
theorem trunc_eq_of_le (X : ℕ → Ω → ℝ) (c : ℝ) {j k : ℕ} (hjk : j ≤ k) (ω : Ω)
    (h : sqSum X k ω ≤ c) : trunc X c j ω = X j ω := by
  unfold trunc
  rw [if_pos ((sqSum_mono X ω hjk).trans h)]

/-- If the squares of the first `n` terms sum to at most `c`, no term among the first `n` is
truncated. -/
theorem sum_trunc_eq_of_sqSum_le (X : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω)
    (h : sqSum X n ω ≤ c) :
    ∑ k ∈ Finset.range n, trunc X c k ω = ∑ k ∈ Finset.range n, X k ω :=
  Finset.sum_congr rfl fun _ hk => trunc_eq_of_le X c (Nat.le_of_lt (Finset.mem_range.1 hk)) ω h

/-- Truncation does not increase the sum of the squares of the first terms. -/
theorem sqSum_trunc_le (X : ℕ → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) :
    sqSum (trunc X c) n ω ≤ sqSum X n ω := by
  unfold sqSum
  refine Finset.sum_le_sum fun k _ => ?_
  dsimp only [trunc]
  split_ifs <;> simp [sq_nonneg]

/-- The indicator of the event that the squares of the first `k` terms sum to at most `c`. -/
private noncomputable def keepIndicator (X : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) : Ω → ℝ :=
  {ω | sqSum X k ω ≤ c}.indicator fun _ => 1

/-- The truncated term is the keeping indicator times the original term. -/
private lemma trunc_eq_keepIndicator_mul (X : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) :
    trunc X c k = keepIndicator X c k * X k := by
  funext ω
  by_cases h : sqSum X k ω ≤ c <;> simp [trunc, keepIndicator, h]

/-- The keeping indicator takes values of norm at most one. -/
private lemma keepIndicator_norm_le (X : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (ω : Ω) :
    ‖keepIndicator X c k ω‖ ≤ 1 := by
  by_cases h : sqSum X k ω ≤ c <;> simp [keepIndicator, h]

/-- Predictable truncation preserves the martingale property of the partial sums. -/
theorem martingale_trunc {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℕ mΩ}
    {X : ℕ → Ω → ℝ}
    (hX : Martingale (fun k ω => ∑ j ∈ Finset.range k, X j ω) ℱ P) (c : ℝ) :
    Martingale (fun k ω => ∑ j ∈ Finset.range k, trunc X c j ω) ℱ P := by
  have hdiff : ∀ j, X j = (fun ω => ∑ k ∈ Finset.range (j + 1), X k ω) -
      fun ω => ∑ k ∈ Finset.range j, X k ω := by
    intro j
    funext ω
    simp [Finset.sum_range_succ]
  have hXsm : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j) := by
    intro j
    rw [hdiff j]
    exact (hX.1 (j + 1)).sub ((hX.1 j).mono (ℱ.mono (Nat.le_succ j)))
  have hXint : ∀ j, Integrable (X j) P := by
    intro j
    rw [hdiff j]
    exact (hX.integrable (j + 1)).sub (hX.integrable j)
  have hsq : ∀ k, StronglyMeasurable[ℱ k] (sqSum X k) := by
    intro k
    unfold sqSum
    convert Finset.stronglyMeasurable_sum (Finset.range k) fun j hj =>
      ((hXsm j).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))).pow 2 using 1
    funext ω
    simp [Finset.sum_apply]
  have hkeep : ∀ k, StronglyMeasurable[ℱ k] (keepIndicator X c k) := by
    intro k
    have hset : MeasurableSet[ℱ k] {ω | sqSum X k ω ≤ c} :=
      (hsq k).measurable (measurableSet_Iic : MeasurableSet (Set.Iic c))
    unfold keepIndicator
    exact stronglyMeasurable_const.indicator hset
  have htsm : ∀ j k, j < k → StronglyMeasurable[ℱ k] (trunc X c j) := by
    intro j k hjk
    rw [trunc_eq_keepIndicator_mul]
    exact ((hkeep j).mono (ℱ.mono hjk.le)).mul
      ((hXsm j).mono (ℱ.mono (Nat.succ_le_of_lt hjk)))
  have htint : ∀ j, Integrable (trunc X c j) P := by
    intro j
    rw [trunc_eq_keepIndicator_mul]
    exact Integrable.bdd_mul (hXint j) ((hkeep j).mono (ℱ.le j)).aestronglyMeasurable
      (ae_of_all _ fun ω => keepIndicator_norm_le X c j ω)
  have hint : ∀ k, Integrable (fun ω => ∑ j ∈ Finset.range k, trunc X c j ω) P := fun k =>
    integrable_finsetSum _ fun j _ => htint j
  have hadp : StronglyAdapted ℱ (fun k ω => ∑ j ∈ Finset.range k, trunc X c j ω) := by
    intro k
    convert Finset.stronglyMeasurable_sum (Finset.range k) fun j hj =>
      htsm j k (Finset.mem_range.1 hj) using 1
    funext ω
    simp [Finset.sum_apply]
  have hcond : ∀ i, P[X i | ℱ i] =ᵐ[P] 0 := by
    intro i
    have hS := condExp_sub (hX.integrable (i + 1)) (hX.integrable i) (ℱ i)
    rw [condExp_of_stronglyMeasurable (ℱ.le i) (hX.1 i) (hX.integrable i)] at hS
    have hS1 := hX.2 i (i + 1) (Nat.le_succ i)
    rw [hdiff i]
    filter_upwards [hS, hS1] with ω h1 h2
    rw [h1]
    simp [h2]
  refine martingale_of_condExp_sub_eq_zero_nat hadp hint fun i => ?_
  have hsum : (fun ω => ∑ j ∈ Finset.range (i + 1), trunc X c j ω) -
      (fun ω => ∑ j ∈ Finset.range i, trunc X c j ω) = trunc X c i := by
    funext ω
    simp [Finset.sum_range_succ]
  rw [hsum, trunc_eq_keepIndicator_mul]
  have h1 := condExp_stronglyMeasurable_mul_of_bound (ℱ.le i) (hkeep i) (hXint i) 1
    (ae_of_all _ fun ω => keepIndicator_norm_le X c i ω)
  filter_upwards [h1, hcond i] with ω h1ω h2ω
  rw [h1ω]
  simp [h2ω]

end LatticeProb.McLeish

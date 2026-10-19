import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Probability.Martingale.Basic

/-!
# Moments of the product `∏ (1 + i t Y k)`

For a real sequence `Y 0, Y 1, …` and a real parameter `t`, the partial products
`∏_{k < n} (1 + i t Y k)` have modulus controlled by `exp (t² ∑ Y k²)`. When the terms are
martingale differences that vanish outside sets on which the partial products are bounded, the
expectation of each partial product equals one.
-/

namespace LatticeProb.McLeish

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The product of `1 + i t Y k` over the first `n` terms. -/
noncomputable def prodOneAddI (Y : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  ∏ k ∈ Finset.range n, (1 + Complex.I * ((t * Y k ω : ℝ) : ℂ))

/-- The squared modulus of `1 + i a` for a real `a` is `1 + a ^ 2`. -/
private lemma norm_one_add_I_mul_sq (a : ℝ) :
    ‖(1 : ℂ) + Complex.I * (a : ℂ)‖ ^ 2 = 1 + a ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The squared modulus of the product is the product of `1 + t ^ 2 Y k ^ 2`. -/
theorem norm_prodOneAddI_sq (Y : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖prodOneAddI Y t n ω‖ ^ 2 = ∏ k ∈ Finset.range n, (1 + t ^ 2 * Y k ω ^ 2) := by
  unfold prodOneAddI
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [norm_one_add_I_mul_sq]
  ring

/-- The product `∏ (1 + t ^ 2 Y k ^ 2)` is at most the exponential of `t ^ 2` times the sum of
the squares. -/
private lemma prod_one_add_sq_le_exp (Y : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ∏ k ∈ Finset.range n, (1 + t ^ 2 * Y k ω ^ 2) ≤
      Real.exp (t ^ 2 * ∑ k ∈ Finset.range n, Y k ω ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
  linarith [Real.add_one_le_exp (t ^ 2 * Y k ω ^ 2)]

/-- The squared modulus of the product is at most `exp (t ^ 2 ∑ Y k ^ 2)`. -/
theorem norm_prodOneAddI_sq_le_exp (Y : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (ω : Ω) :
    ‖prodOneAddI Y t n ω‖ ^ 2 ≤ Real.exp (t ^ 2 * ∑ k ∈ Finset.range n, Y k ω ^ 2) := by
  rw [norm_prodOneAddI_sq]
  exact prod_one_add_sq_le_exp Y t n ω

/-- If the squares of the earlier terms sum to at most `c` whenever a term is nonzero, and every
term square is at most `M`, then the product `∏ (1 + t ^ 2 Y k ^ 2)` is at most
`exp (t ^ 2 c) (1 + t ^ 2 M)`. -/
private lemma prod_one_add_sq_le (Y : ℕ → Ω → ℝ) (t c M : ℝ) (n : ℕ) (ω : Ω)
    (hc0 : 0 ≤ c) (hM0 : 0 ≤ M)
    (hc : ∀ k < n, Y k ω ≠ 0 → ∑ j ∈ Finset.range k, Y j ω ^ 2 ≤ c)
    (hM : ∀ k < n, Y k ω ^ 2 ≤ M) :
    ∏ k ∈ Finset.range n, (1 + t ^ 2 * Y k ω ^ 2) ≤
      Real.exp (t ^ 2 * c) * (1 + t ^ 2 * M) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty]
    have h1 : 1 ≤ Real.exp (t ^ 2 * c) := Real.one_le_exp (mul_nonneg (sq_nonneg t) hc0)
    have h2 : 1 ≤ 1 + t ^ 2 * M := le_add_of_nonneg_right (mul_nonneg (sq_nonneg t) hM0)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have ih' := ih (fun k hk => hc k (by omega)) (fun k hk => hM k (by omega))
    by_cases h : Y n ω = 0
    · rw [h]
      simpa using ih'
    · have hcn := hc n (by omega) h
      have hP : ∏ k ∈ Finset.range n, (1 + t ^ 2 * Y k ω ^ 2) ≤ Real.exp (t ^ 2 * c) :=
        (prod_one_add_sq_le_exp Y t n ω).trans
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hcn (sq_nonneg t)))
      have hfac : 1 + t ^ 2 * Y n ω ^ 2 ≤ 1 + t ^ 2 * M := by
        linarith [mul_le_mul_of_nonneg_left (hM n (by omega)) (sq_nonneg t)]
      exact mul_le_mul hP hfac (by positivity) (Real.exp_nonneg _)

/-- Under the same bounds, the squared modulus of the product is at most
`exp (t ^ 2 c) (1 + t ^ 2 M)`. -/
theorem norm_prodOneAddI_sq_le (Y : ℕ → Ω → ℝ) (t c M : ℝ) (n : ℕ) (ω : Ω)
    (hc0 : 0 ≤ c) (hM0 : 0 ≤ M)
    (hc : ∀ k < n, Y k ω ≠ 0 → ∑ j ∈ Finset.range k, Y j ω ^ 2 ≤ c)
    (hM : ∀ k < n, Y k ω ^ 2 ≤ M) :
    ‖prodOneAddI Y t n ω‖ ^ 2 ≤ Real.exp (t ^ 2 * c) * (1 + t ^ 2 * M) := by
  rw [norm_prodOneAddI_sq]
  exact prod_one_add_sq_le Y t c M n ω hc0 hM0 hc hM

/-- Since `Y n` vanishes off `A`, the product over the first `n + 1` terms is the product over the
first `n` terms plus `i t` times `Y n` times the indicator of `A` applied to that product. -/
private lemma prodOneAddI_succ (Y : ℕ → Ω → ℝ) (t : ℝ) (n : ℕ) (A : Set Ω)
    (hzero : ∀ ω, ω ∉ A → Y n ω = 0) (ω : Ω) :
    prodOneAddI Y t (n + 1) ω =
      prodOneAddI Y t n ω +
        Complex.I * t * ((Y n ω : ℂ) * A.indicator (prodOneAddI Y t n) ω) := by
  by_cases h : ω ∈ A
  · simp only [Set.indicator_of_mem h, prodOneAddI, Finset.prod_range_succ]
    push_cast
    ring
  · have hY0 := hzero ω h
    simp [h, prodOneAddI, Finset.prod_range_succ, hY0]

/-- The norm of an indicator of a family bounded by `C` on its set is at most `max C 0`. -/
private lemma norm_indicator_le (A : Set Ω) (f : Ω → ℂ) (C : ℝ)
    (hf : ∀ ω, ω ∈ A → ‖f ω‖ ≤ C)
    (ω : Ω) : ‖A.indicator f ω‖ ≤ max C 0 := by
  by_cases h : ω ∈ A
  · simp only [Set.indicator_of_mem h]
    exact (hf ω h).trans (le_max_left _ _)
  · simp [h]

/-- The increments of a martingale of partial sums are strongly measurable one step ahead. -/
private lemma sm_increment {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : Martingale (fun k ω => ∑ j ∈ Finset.range k, Y j ω) ℱ P) (j : ℕ) :
    StronglyMeasurable[ℱ (j + 1)] (Y j) := by
  have hdiff : Y j = (fun ω => ∑ k ∈ Finset.range (j + 1), Y k ω) -
      fun ω => ∑ k ∈ Finset.range j, Y k ω := by
    funext ω
    simp [Finset.sum_range_succ]
  rw [hdiff]
  exact (hY.1 (j + 1)).sub ((hY.1 j).mono (ℱ.mono (Nat.le_succ j)))

/-- The increments of a martingale of partial sums are integrable. -/
private lemma integrable_increment {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ}
    (hY : Martingale (fun k ω => ∑ j ∈ Finset.range k, Y j ω) ℱ P) (j : ℕ) :
    Integrable (Y j) P := by
  have hdiff : Y j = (fun ω => ∑ k ∈ Finset.range (j + 1), Y k ω) -
      fun ω => ∑ k ∈ Finset.range j, Y k ω := by
    funext ω
    simp [Finset.sum_range_succ]
  rw [hdiff]
  exact (hY.integrable (j + 1)).sub (hY.integrable j)

/-- The conditional expectation of an increment of a martingale of partial sums given the
earlier past vanishes. -/
private lemma condExp_increment_eq_zero {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : Martingale (fun k ω => ∑ j ∈ Finset.range k, Y j ω) ℱ P) (j : ℕ) :
    P[Y j | ℱ j] =ᵐ[P] 0 := by
  have hdiff : Y j = (fun ω => ∑ k ∈ Finset.range (j + 1), Y k ω) -
      fun ω => ∑ k ∈ Finset.range j, Y k ω := by
    funext ω
    simp [Finset.sum_range_succ]
  have hS := condExp_sub (hY.integrable (j + 1)) (hY.integrable j) (ℱ j)
  rw [condExp_of_stronglyMeasurable (ℱ.le j) (hY.1 j) (hY.integrable j)] at hS
  have hS1 := hY.2 j (j + 1) (Nat.le_succ j)
  rw [hdiff]
  filter_upwards [hS, hS1] with ω h1 h2
  rw [h1]
  simp [h2]

/-- Multiplication of a complex number by a real scalar, as a continuous bilinear map. -/
private noncomputable def mulRC : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).comp Complex.ofRealCLM).flip

private lemma mulRC_apply (z : ℂ) (x : ℝ) : mulRC z x = (x : ℂ) * z := rfl

/-- Multiplying an increment of a martingale by a bounded factor that is measurable at the
earlier time gives an integrable function. -/
private lemma integrable_increment_mul {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : Martingale (fun k ω => ∑ j ∈ Finset.range k, Y j ω) ℱ P) (n : ℕ)
    (f : Ω → ℂ)
    (hfm : StronglyMeasurable[ℱ n] f) (c : ℝ) (hfc : ∀ ω, ‖f ω‖ ≤ c) :
    Integrable (fun ω => (Y n ω : ℂ) * f ω) P := by
  have hYc : Integrable (fun ω => (Y n ω : ℂ)) P := (integrable_increment hY n).ofReal
  exact hYc.mul_bdd (hfm.mono (ℱ.le n)).aestronglyMeasurable (ae_of_all _ hfc)

/-- The integral of an increment times a bounded factor measurable at the earlier time is zero. -/
private lemma integral_increment_mul_eq_zero {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : Martingale (fun k ω => ∑ j ∈ Finset.range k, Y j ω) ℱ P) (n : ℕ)
    (f : Ω → ℂ)
    (hfm : StronglyMeasurable[ℱ n] f) (c : ℝ) (hfc : ∀ ω, ‖f ω‖ ≤ c) :
    ∫ ω, (Y n ω : ℂ) * f ω ∂P = 0 := by
  have hint : Integrable (fun ω => mulRC (f ω) (Y n ω)) P :=
    integrable_increment_mul hY n f hfm c hfc
  have hg : Integrable (Y n) P := integrable_increment hY n
  have hcond := condExp_bilin_of_stronglyMeasurable_left mulRC hfm hint hg
  have hzero := condExp_increment_eq_zero hY n
  calc ∫ ω, (Y n ω : ℂ) * f ω ∂P = ∫ ω, mulRC (f ω) (Y n ω) ∂P := by
        simp only [mulRC_apply, mul_comm]
    _ = ∫ ω, (P[fun ω => mulRC (f ω) (Y n ω) | ℱ n]) ω ∂P :=
        (integral_condExp (ℱ.le n)).symm
    _ = ∫ ω, mulRC (f ω) ((P[Y n | ℱ n]) ω) ∂P := integral_congr_ae hcond
    _ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hzero] with ω hω
        simp [hω]

/-- The product `∏ (1 + i t Y k)` is strongly measurable at the time `n` of the filtration. -/
theorem stronglyMeasurable_prodOneAddI {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ}
    (hY : ∀ k, StronglyMeasurable[ℱ (k + 1)] (Y k)) (t : ℝ) (n : ℕ) :
    StronglyMeasurable[ℱ n] (prodOneAddI Y t n) := by
  induction n with
  | zero =>
    have h0 : prodOneAddI Y t 0 = fun _ => 1 := by
      funext ω
      simp [prodOneAddI]
    rw [h0]
    exact stronglyMeasurable_const
  | succ n ih =>
    have hfac : StronglyMeasurable[ℱ (n + 1)]
        (fun ω => (1 : ℂ) + Complex.I * ((t * Y n ω : ℝ) : ℂ)) :=
      stronglyMeasurable_const.add (stronglyMeasurable_const.mul
        (Continuous.comp_stronglyMeasurable (g := fun x : ℝ => ((t * x : ℝ) : ℂ))
          (by fun_prop) (hY n)))
    have hprod : prodOneAddI Y t (n + 1) =
        fun ω => prodOneAddI Y t n ω * (1 + Complex.I * ((t * Y n ω : ℝ) : ℂ)) := by
      funext ω
      simp only [prodOneAddI, Finset.prod_range_succ]
    rw [hprod]
    exact (ih.mono (ℱ.mono (Nat.le_succ n))).mul hfac

/-- The product `∏ (1 + i t Y k)` is integrable when the increments are controlled by the
martingale and the factors are bounded on the sets `A k`, where the increments vanish outside. -/
theorem integrable_prodOneAddI {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : MeasureTheory.Martingale (fun k ω => ∑ j ∈ Finset.range k, Y j ω) ℱ P)
    (t C : ℝ) (A : ℕ → Set Ω) (hA : ∀ k, MeasurableSet[ℱ k] (A k))
    (hzero : ∀ k, ∀ ω, ω ∉ A k → Y k ω = 0)
    (hbound : ∀ k, ∀ ω, ω ∈ A k → ‖prodOneAddI Y t k ω‖ ≤ C) (n : ℕ) :
    MeasureTheory.Integrable (prodOneAddI Y t n) P := by
  induction n with
  | zero =>
    have h0 : prodOneAddI Y t 0 = fun _ => 1 := by
      funext ω
      simp [prodOneAddI]
    rw [h0]
    exact integrable_const 1
  | succ n ih =>
    have hfm : StronglyMeasurable[ℱ n] ((A n).indicator (prodOneAddI Y t n)) :=
      (stronglyMeasurable_prodOneAddI (fun k => sm_increment hY k) t n).indicator (hA n)
    have hG := integrable_increment_mul hY n _ hfm (max C 0)
      (norm_indicator_le (A n) (prodOneAddI Y t n) C (hbound n))
    have hfun : prodOneAddI Y t (n + 1) = fun ω => prodOneAddI Y t n ω +
        Complex.I * t * ((Y n ω : ℂ) * (A n).indicator (prodOneAddI Y t n) ω) :=
      funext fun ω => prodOneAddI_succ Y t n (A n) (hzero n) ω
    rw [hfun]
    exact ih.add (hG.const_mul _)

/-- The product `∏ (1 + i t Y k)` has expectation one under the same hypotheses. -/
theorem integral_prodOneAddI {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ}
    (hY : MeasureTheory.Martingale (fun k ω => ∑ j ∈ Finset.range k, Y j ω) ℱ P)
    (t C : ℝ) (A : ℕ → Set Ω) (hA : ∀ k, MeasurableSet[ℱ k] (A k))
    (hzero : ∀ k, ∀ ω, ω ∉ A k → Y k ω = 0)
    (hbound : ∀ k, ∀ ω, ω ∈ A k → ‖prodOneAddI Y t k ω‖ ≤ C) (n : ℕ) :
    ∫ ω, prodOneAddI Y t n ω ∂P = 1 := by
  induction n with
  | zero =>
    have h0 : prodOneAddI Y t 0 = fun _ => 1 := by
      funext ω
      simp [prodOneAddI]
    rw [h0]
    simp
  | succ n ih =>
    have hfm : StronglyMeasurable[ℱ n] ((A n).indicator (prodOneAddI Y t n)) :=
      (stronglyMeasurable_prodOneAddI (fun k => sm_increment hY k) t n).indicator (hA n)
    have hG := integrable_increment_mul hY n _ hfm (max C 0)
      (norm_indicator_le (A n) (prodOneAddI Y t n) C (hbound n))
    have hfun : prodOneAddI Y t (n + 1) = fun ω => prodOneAddI Y t n ω +
        Complex.I * t * ((Y n ω : ℂ) * (A n).indicator (prodOneAddI Y t n) ω) :=
      funext fun ω => prodOneAddI_succ Y t n (A n) (hzero n) ω
    have hPint := integrable_prodOneAddI hY t C A hA hzero hbound n
    rw [hfun, integral_add hPint (hG.const_mul _), integral_const_mul,
      integral_increment_mul_eq_zero hY n _ hfm (max C 0)
        (norm_indicator_le (A n) (prodOneAddI Y t n) C (hbound n)), ih]
    simp

end LatticeProb.McLeish

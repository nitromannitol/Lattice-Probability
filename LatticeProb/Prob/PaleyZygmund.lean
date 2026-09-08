/-
The Paley-Zygmund inequality.

A nonnegative square-integrable variable exceeds a fraction of its mean with a
probability bounded below by the ratio of its two moments:

  `P(X > θ E X) ≥ (1-θ)^2 (E X)^2 / E X^2`   for `0 ≤ θ ≤ 1`.

The proof is one line of bookkeeping and one Cauchy-Schwarz, which is
`LatticeProb.abs_integral_mul_le` of `LatticeProb/Prob/EfronSteinCov.lean`.
Splitting `E X` over the event `A = {X > θ E X}` and its complement bounds
`E X ≤ θ E X + E[X 1_A]`, so `(1-θ) E X ≤ E[X 1_A] ≤ (E X^2)^{1/2} P(A)^{1/2}`,
and squaring is legitimate because `θ ≤ 1` makes the left side nonnegative.

The corollary recorded with it is the form a second-moment bound is used in: if
`E X^2 ≤ 2 (E X)^2` then `P(X > θ E X) ≥ (1-θ)^2/2`, a bound with no dependence
on the law at all.  That is the shape in which the second moment of the range of
the walk, `LatticeProb.integral_rangeCard_sq_le`, is turned into a lower bound on
the probability that the range is large.
-/
import Mathlib
import LatticeProb.Prob.EfronSteinCov

noncomputable section

namespace LatticeProb

open MeasureTheory

theorem paley_zygmund {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {X : α → ℝ} (hXm : Measurable X) (hXnn : ∀ x, 0 ≤ X x)
    (hX2 : Integrable (fun x => X x ^ 2) P) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ x, X x ∂P) ^ 2
      ≤ (∫ x, X x ^ 2 ∂P) * P.real {x | θ * (∫ x, X x ∂P) < X x} := by
  classical
  set m : ℝ := ∫ x, X x ∂P with hmdef
  set A : Set α := {x | θ * m < X x} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_lt measurable_const hXm
  set f : α → ℝ := A.indicator (fun _ => (1 : ℝ)) with hfdef
  have hfm : Measurable f := measurable_const.indicator hAmeas
  have hX1 : Integrable X P := integrable_of_integrable_sq P hXm.aestronglyMeasurable hX2
  have hm0 : (0 : ℝ) ≤ m := integral_nonneg hXnn
  have hf2 : (fun x => f x ^ 2) = f := by
    funext x
    by_cases h : x ∈ A
    · simp [hfdef, Set.indicator_of_mem h]
    · simp [hfdef, Set.indicator_of_notMem h]
  have hfint : Integrable f P := (integrable_const (1 : ℝ)).indicator hAmeas
  have hfint2 : Integrable (fun x => f x ^ 2) P := by rw [hf2]; exact hfint
  have hXf : Integrable (fun x => X x * f x) P :=
    integrable_mul_of_sq hXm.aestronglyMeasurable hfm.aestronglyMeasurable hX2 hfint2
  have hpt : ∀ x, X x ≤ θ * m + X x * f x := by
    intro x
    by_cases h : x ∈ A
    · have : f x = 1 := by simp [hfdef, Set.indicator_of_mem h]
      rw [this, mul_one]
      nlinarith [hθ0, hm0]
    · have hf0 : f x = 0 := by simp [hfdef, Set.indicator_of_notMem h]
      have hle : X x ≤ θ * m := by
        rw [hAdef, Set.mem_setOf_eq] at h
        exact not_lt.mp h
      rw [hf0, mul_zero, add_zero]
      exact hle
  have hint : m ≤ θ * m + ∫ x, X x * f x ∂P := by
    have := integral_mono_ae hX1 ((integrable_const (θ * m)).add hXf)
      (Filter.Eventually.of_forall hpt)
    simpa [integral_add (integrable_const (θ * m)) hXf] using this
  have hlow : (1 - θ) * m ≤ ∫ x, X x * f x ∂P := by linarith
  have hCS := abs_integral_mul_le (P := P) hXm.aestronglyMeasurable hfm.aestronglyMeasurable
    hX2 hfint2
  have hfA : ∫ x, f x ∂P = P.real A := by
    rw [hfdef, integral_indicator_const (1 : ℝ) hAmeas]
    simp [measureReal_def]
  have hf2A : ∫ x, f x ^ 2 ∂P = P.real A := by rw [hf2]; exact hfA
  have hS0 : (0 : ℝ) ≤ ∫ x, X x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hA0 : (0 : ℝ) ≤ P.real A := measureReal_nonneg
  rw [hf2A] at hCS
  have hbound : (1 - θ) * m ≤ Real.sqrt (∫ x, X x ^ 2 ∂P) * Real.sqrt (P.real A) :=
    le_trans (le_trans hlow (le_abs_self _)) hCS
  have hsq1 : Real.sqrt (∫ x, X x ^ 2 ∂P) ^ 2 = ∫ x, X x ^ 2 ∂P := Real.sq_sqrt hS0
  have hsq2 : Real.sqrt (P.real A) ^ 2 = P.real A := Real.sq_sqrt hA0
  have hnn : (0 : ℝ) ≤ (1 - θ) * m := mul_nonneg (by linarith) hm0
  have hsq := mul_self_le_mul_self hnn hbound
  nlinarith [hsq, hsq1, hsq2]

/-- **Paley-Zygmund with a second-moment bound.**  When the second moment is at
most twice the square of the mean, the variable exceeds `θ` times its mean with
probability at least `(1-θ)^2/2`, uniformly in the law. -/
theorem paley_zygmund_of_second_moment {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {X : α → ℝ} (hXm : Measurable X) (hXnn : ∀ x, 0 ≤ X x)
    (hX2 : Integrable (fun x => X x ^ 2) P) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmpos : 0 < ∫ x, X x ∂P) (hsecond : (∫ x, X x ^ 2 ∂P) ≤ 2 * (∫ x, X x ∂P) ^ 2) :
    (1 - θ) ^ 2 / 2 ≤ P.real {x | θ * (∫ x, X x ∂P) < X x} := by
  have hPZ := paley_zygmund P hXm hXnn hX2 hθ0 hθ1
  have hq : (0 : ℝ) ≤ P.real {x | θ * (∫ x, X x ∂P) < X x} := measureReal_nonneg
  have hm2 : (0 : ℝ) < (∫ x, X x ∂P) ^ 2 := pow_pos hmpos 2
  nlinarith [hPZ, mul_le_mul_of_nonneg_right hsecond hq, hq, hm2, sq_nonneg (1 - θ)]

end LatticeProb

import Mathlib
import LatticeProb.LQG.LQGCircleMoments

/-!
# Decoupling of products of circle-average densities in the unit disc

For the circle-average density `ε^{γ²/2} e^{γ h_ε(x)}` of the whole-plane GFF, the expectation of a product of
densities at finitely many points inside the unit disc is `exp (γ² ∑_{k<l} Cov(h_ε(x_k), h_ε(x_l)))`.
For two families of points `x_j` and `y_k` the expectation of the product over both families is
(expectation over `x`) · (expectation over `y`) · `exp (γ² ∑_j ∑_k Cov(h_ε(x_j), h_ε(y_k)))`, and
when the families are at distance at least `r` from each other, the last factor is at most
`(2/r)^(γ² |x| |y|)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The circle-average density `ε^{γ²/2} exp (γ h_ε(x))` of the approximate Liouville measure. -/
noncomputable def gmcDensity (hcirc : Ω → ℝ → ℂ → ℝ) (γ ε : ℝ) (x : ℂ) (ω : Ω) : ℝ :=
  ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε x)

theorem gmcDensity_nonneg (hcirc : Ω → ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (x : ℂ) (ω : Ω) :
    0 ≤ gmcDensity hcirc γ ε x ω :=
  mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le

/-- A product of circle-average densities is a power of `ε` times the exponential of a sum. -/
theorem prod_gmcDensity {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (x : ι → ℂ)
    (ω : Ω) :
    ∏ j, gmcDensity hcirc γ ε (x j) ω =
      ε ^ (γ ^ 2 / 2 * (Fintype.card ι : ℝ)) * Real.exp (∑ j, γ * hcirc ω ε (x j)) := by
  simp only [gmcDensity]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum,
    ← Real.rpow_natCast, ← Real.rpow_mul hε.le]

/-- The expectation of a product of circle-average densities. -/
theorem IsWholePlaneGFF.integral_prod_gmcDensity (hh : IsWholePlaneGFF P hC hcirc)
    {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (x : ι → ℂ) :
    ∫ ω, ∏ j, gmcDensity hcirc γ ε (x j) ω ∂P =
      ε ^ (γ ^ 2 / 2 * (Fintype.card ι : ℝ)) * Real.exp ((∑ j, ∑ l, γ * γ *
        cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (x l); P]) / 2) := by
  simp_rw [prod_gmcDensity hε]
  rw [integral_const_mul]
  exact congrArg _ (hh.integral_exp_sum_circle hε x (fun _ => γ))

/-- **Exact decoupling of two families of circle-average densities.** -/
theorem IsWholePlaneGFF.integral_prod_gmcDensity_two (hh : IsWholePlaneGFF P hC hcirc)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (x : ι₁ → ℂ)
    (y : ι₂ → ℂ) :
    ∫ ω, (∏ j, gmcDensity hcirc γ ε (x j) ω) * ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P =
      (∫ ω, ∏ j, gmcDensity hcirc γ ε (x j) ω ∂P) *
        (∫ ω, ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P) *
        Real.exp (γ ^ 2 * ∑ j, ∑ k,
          cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P]) := by
  have key : ∀ ω, (∏ j, gmcDensity hcirc γ ε (x j) ω) * ∏ k, gmcDensity hcirc γ ε (y k) ω =
      ∏ s : ι₁ ⊕ ι₂, gmcDensity hcirc γ ε (Sum.elim x y s) ω := fun ω => by
    rw [Fintype.prod_sum_type]; simp
  simp_rw [key]
  rw [hh.integral_prod_gmcDensity hε γ (Sum.elim x y), hh.integral_prod_gmcDensity hε γ x,
    hh.integral_prod_gmcDensity hε γ y]
  simp only [Fintype.card_sum, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Nat.cast_add,
    Finset.sum_add_distrib]
  have hsymm : ∑ k, ∑ j, γ * γ * cov[fun ω => hcirc ω ε (y k), fun ω => hcirc ω ε (x j); P] =
      ∑ j, ∑ k, γ * γ * cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P] := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [covariance_comm]
  rw [hsymm]
  have hS : ∑ j, ∑ k, γ * γ * cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P] =
      γ ^ 2 * ∑ j, ∑ k, cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P] := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hS, mul_add (γ ^ 2 / 2), Real.rpow_add hε]
  set A := ∑ j, ∑ l, γ * γ * cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (x l); P]
  set D := ∑ k, ∑ l, γ * γ * cov[fun ω => hcirc ω ε (y k), fun ω => hcirc ω ε (y l); P]
  set B := γ ^ 2 * ∑ j, ∑ k, cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P]
  have : (A + B + (B + D)) / 2 = A / 2 + D / 2 + B := by ring
  rw [this, Real.exp_add, Real.exp_add]
  ring

/-- **Decoupling bound for circle-average densities at separated points.** If the circles of radius `ε`
around the points `x j` and `y k` lie in the closed unit disc and `‖x j - y k‖ ≥ r > 0`, then
`E[∏_j f(x_j) ∏_k f(y_k)] ≤ (2/r)^(γ² |x| |y|) E[∏_j f(x_j)] E[∏_k f(y_k)]`
for the densities `f(x) = ε^{γ²/2} exp (γ h_ε(x))`. -/
theorem IsWholePlaneGFF.integral_prod_gmcDensity_two_le (hh : IsWholePlaneGFF P hC hcirc)
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (x : ι₁ → ℂ) (y : ι₂ → ℂ) (hx : ∀ j, ‖x j‖ + ε ≤ 1) (hy : ∀ k, ‖y k‖ + ε ≤ 1)
    (hxy : ∀ j k, r ≤ ‖x j - y k‖) :
    ∫ ω, (∏ j, gmcDensity hcirc γ ε (x j) ω) * ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P ≤
      (2 / r) ^ (γ ^ 2 * ((Fintype.card ι₁ : ℝ) * Fintype.card ι₂)) *
        ((∫ ω, ∏ j, gmcDensity hcirc γ ε (x j) ω ∂P) *
          ∫ ω, ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P) := by
  rw [hh.integral_prod_gmcDensity_two hε γ x y]
  have hI1 : 0 ≤ ∫ ω, ∏ j, gmcDensity hcirc γ ε (x j) ω ∂P :=
    integral_nonneg fun ω => Finset.prod_nonneg fun j _ => gmcDensity_nonneg hcirc hε γ _ ω
  have hI2 : 0 ≤ ∫ ω, ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P :=
    integral_nonneg fun ω => Finset.prod_nonneg fun k _ => gmcDensity_nonneg hcirc hε γ _ ω
  have hcov : ∀ j k, cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P] ≤
      Real.log 2 - Real.log r := fun j k => by
    have hne : x j ≠ y k := by
      intro h
      have := hxy j k
      rw [h, sub_self, norm_zero] at this
      linarith
    have h1 := hh.covariance_circle_le_log_two hε (hx j) (hy k) hne
    have := Real.log_le_log hr (hxy j k)
    linarith
  have hsum : ∑ j, ∑ k, cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P] ≤
      ((Fintype.card ι₁ : ℝ) * Fintype.card ι₂) * (Real.log 2 - Real.log r) := by
    calc _ ≤ ∑ _j : ι₁, ∑ _k : ι₂, (Real.log 2 - Real.log r) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hcov j k
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hexp : Real.exp (γ ^ 2 * ∑ j, ∑ k,
      cov[fun ω => hcirc ω ε (x j), fun ω => hcirc ω ε (y k); P]) ≤
      (2 / r) ^ (γ ^ 2 * ((Fintype.card ι₁ : ℝ) * Fintype.card ι₂)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div two_ne_zero hr.ne']
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hsum (sq_nonneg γ)
    nlinarith
  calc _ ≤ (∫ ω, ∏ j, gmcDensity hcirc γ ε (x j) ω ∂P) *
        (∫ ω, ∏ k, gmcDensity hcirc γ ε (y k) ω ∂P) *
        (2 / r) ^ (γ ^ 2 * ((Fintype.card ι₁ : ℝ) * Fintype.card ι₂)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hI1 hI2)
    _ = _ := by ring

end LatticeProb.Gauss

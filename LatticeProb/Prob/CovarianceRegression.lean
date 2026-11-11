import Mathlib.Probability.Moments.Variance

/-!
# Linear regression on pairwise uncorrelated random variables and Bessel's inequality

Let `η k`, `k ∈ s`, be pairwise uncorrelated square integrable real random variables and `Y` a square integrable
random variable. The linear regression of `Y` on the family is `∑ k ∈ s, (Var[η k])⁻¹ * cov[Y, η k] * η k`
(with the convention `0⁻¹ = 0`, which is harmless because `cov[Y, η k] = 0` when `Var[η k] = 0`).

* `LatticeProb.covariance_eq_zero_of_variance_eq_zero_right`: a random variable of variance zero is uncorrelated
  with every random variable.
* `LatticeProb.covariance_fun_sum_const_mul_left`: the covariance of a linear combination.
* `LatticeProb.variance_fun_sum_const_mul_of_covariance_eq_zero`: the variance of a linear combination of pairwise
  uncorrelated random variables.
* `LatticeProb.covariance_sub_regression_eq_zero`: the regression residual is uncorrelated with each `η l`, `l ∈ s`.
* `LatticeProb.variance_regression`, `LatticeProb.variance_sub_regression`: the variances of the regression and of
  its residual.
* `LatticeProb.sum_inv_variance_mul_covariance_sq_le_variance`: Bessel's inequality
  `∑ k ∈ s, (Var[η k])⁻¹ * cov[Y, η k] ^ 2 ≤ Var[Y]`.
* `LatticeProb.summable_inv_variance_mul_covariance_sq`: for a sequence of pairwise uncorrelated random variables
  the series of Bessel's inequality is summable.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {Ω κ : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A square integrable random variable of variance zero is uncorrelated with every random variable. -/
theorem covariance_eq_zero_of_variance_eq_zero_right [IsFiniteMeasure P] (X : Ω → ℝ) {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) (h : Var[Y; P] = 0) : cov[X, Y; P] = 0 := by
  have hae : (fun ω => (X ω - P[X]) * (Y ω - P[Y])) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [ae_eq_integral_of_variance_eq_zero hY h] with ω hω
    rw [hω, sub_self, mul_zero]
  rw [covariance, integral_congr_ae hae, integral_zero]

/-- The covariance of a linear combination with a random variable. -/
theorem covariance_fun_sum_const_mul_left [IsFiniteMeasure P] {s : Finset κ} {η : κ → Ω → ℝ}
    (hη : ∀ k ∈ s, MemLp (η k) 2 P) {W : Ω → ℝ} (hW : MemLp W 2 P) (a : κ → ℝ) :
    cov[fun ω => ∑ k ∈ s, a k * η k ω, W; P] = ∑ k ∈ s, a k * cov[η k, W; P] := by
  rw [covariance_fun_sum_left' (X := fun k ω => a k * η k ω) (fun k hk => (hη k hk).const_mul (a k)) hW]
  exact Finset.sum_congr rfl fun k _ => covariance_const_mul_left (a k)

/-- The variance of a linear combination of pairwise uncorrelated random variables. -/
theorem variance_fun_sum_const_mul_of_covariance_eq_zero [IsFiniteMeasure P] {s : Finset κ} {η : κ → Ω → ℝ}
    (hη : ∀ k ∈ s, MemLp (η k) 2 P) (horth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → cov[η k, η l; P] = 0) (a : κ → ℝ) :
    Var[fun ω => ∑ k ∈ s, a k * η k ω; P] = ∑ k ∈ s, a k ^ 2 * Var[η k; P] := by
  rw [variance_fun_sum' (X := fun k ω => a k * η k ω) fun k hk => (hη k hk).const_mul (a k)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hterm : ∀ l, cov[fun ω => a k * η k ω, fun ω => a l * η l ω; P] = a k * (a l * cov[η k, η l; P]) :=
    fun l => by rw [covariance_const_mul_left, covariance_const_mul_right]
  rw [Finset.sum_eq_single_of_mem k hk]
  · rw [hterm, covariance_self (hη k hk).aemeasurable]
    ring
  · intro l hl hlk
    rw [hterm, horth k hk l hl (Ne.symm hlk), mul_zero, mul_zero]

private lemma inv_mul_sq_mul_self (V c : ℝ) : (V⁻¹ * c) ^ 2 * V = V⁻¹ * c ^ 2 := by
  by_cases h0 : V = 0
  · simp [h0]
  · have hV : V⁻¹ * V = 1 := inv_mul_cancel₀ h0
    calc (V⁻¹ * c) ^ 2 * V = V⁻¹ * c ^ 2 * (V⁻¹ * V) := by ring
      _ = V⁻¹ * c ^ 2 := by rw [hV, mul_one]

/-- The variance of the linear regression of `Y` on pairwise uncorrelated random variables. -/
theorem variance_regression [IsFiniteMeasure P] {s : Finset κ} (Y : Ω → ℝ) {η : κ → Ω → ℝ}
    (hη : ∀ k ∈ s, MemLp (η k) 2 P) (horth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → cov[η k, η l; P] = 0) :
    Var[fun ω => ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω; P] =
      ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 := by
  rw [variance_fun_sum_const_mul_of_covariance_eq_zero hη horth]
  exact Finset.sum_congr rfl fun k _ => inv_mul_sq_mul_self _ _

/-- The residual of the linear regression of `Y` on pairwise uncorrelated random variables `η k`, `k ∈ s`, is
uncorrelated with each `η l`, `l ∈ s`. -/
theorem covariance_sub_regression_eq_zero [IsFiniteMeasure P] {s : Finset κ} {Y : Ω → ℝ} {η : κ → Ω → ℝ}
    (hY : MemLp Y 2 P) (hη : ∀ k ∈ s, MemLp (η k) 2 P)
    (horth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → cov[η k, η l; P] = 0) {l : κ} (hl : l ∈ s) :
    cov[fun ω => Y ω - ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω, η l; P] = 0 := by
  have hT : MemLp (fun ω => ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω) 2 P :=
    memLp_finsetSum s fun k hk => (hη k hk).const_mul _
  rw [covariance_fun_sub_left hY hT (hη l hl), covariance_fun_sum_const_mul_left hη (hη l hl),
    Finset.sum_eq_single_of_mem l hl, covariance_self (hη l hl).aemeasurable]
  · by_cases h0 : Var[η l; P] = 0
    · rw [covariance_eq_zero_of_variance_eq_zero_right Y (hη l hl) h0, h0]
      simp
    · rw [mul_right_comm, inv_mul_cancel₀ h0, one_mul, sub_self]
  · intro k hk hkl
    rw [horth k hk l hl hkl, mul_zero]

/-- The variance of the residual of the linear regression of `Y` on pairwise uncorrelated random variables. -/
theorem variance_sub_regression [IsFiniteMeasure P] {s : Finset κ} {Y : Ω → ℝ} {η : κ → Ω → ℝ}
    (hY : MemLp Y 2 P) (hη : ∀ k ∈ s, MemLp (η k) 2 P)
    (horth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → cov[η k, η l; P] = 0) :
    Var[fun ω => Y ω - ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω; P] =
      Var[Y; P] - ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 := by
  have hT : MemLp (fun ω => ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω) 2 P :=
    memLp_finsetSum s fun k hk => (hη k hk).const_mul _
  have hcov : cov[Y, fun ω => ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω; P] =
      ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 := by
    rw [covariance_comm, covariance_fun_sum_const_mul_left hη hY]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [covariance_comm (η k) Y]
    ring
  have hsub := variance_sub hY hT
  rw [hcov, variance_regression Y hη horth] at hsub
  have hfun : (fun ω => Y ω - ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω) =
      Y - fun ω => ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω := rfl
  rw [hfun, hsub]
  ring

/-- **Bessel's inequality** for pairwise uncorrelated random variables. -/
theorem sum_inv_variance_mul_covariance_sq_le_variance [IsFiniteMeasure P] {s : Finset κ} {Y : Ω → ℝ}
    {η : κ → Ω → ℝ} (hY : MemLp Y 2 P) (hη : ∀ k ∈ s, MemLp (η k) 2 P)
    (horth : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → cov[η k, η l; P] = 0) :
    ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 ≤ Var[Y; P] := by
  have h := variance_nonneg (fun ω => Y ω - ∑ k ∈ s, (Var[η k; P])⁻¹ * cov[Y, η k; P] * η k ω) P
  rw [variance_sub_regression hY hη horth] at h
  linarith

/-- For a sequence of pairwise uncorrelated random variables, the series of Bessel's inequality is summable. -/
theorem summable_inv_variance_mul_covariance_sq [IsFiniteMeasure P] {Y : Ω → ℝ} {η : ℕ → Ω → ℝ}
    (hY : MemLp Y 2 P) (hη : ∀ k, MemLp (η k) 2 P) (horth : ∀ k l, k ≠ l → cov[η k, η l; P] = 0) :
    Summable fun k => (Var[η k; P])⁻¹ * cov[Y, η k; P] ^ 2 :=
  summable_of_sum_range_le (c := Var[Y; P])
    (fun _ => mul_nonneg (inv_nonneg.mpr (variance_nonneg _ _)) (sq_nonneg _))
    fun _ => sum_inv_variance_mul_covariance_sq_le_variance hY (fun k _ => hη k) fun k _ l _ h => horth k l h

end LatticeProb

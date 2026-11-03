/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.KahaneCore at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.KahaneStein

/-!
# Kahane's convexity inequality: the interpolation and its bounds

Notation for the Gaussian interpolation of J.-P. Kahane, *Sur le chaos multiplicatif*,
Ann. Sci. Math. Québec 9 (1985) 105–150, in the form of N. Berestycki and E. Powell,
*Gaussian free field and Liouville quantum gravity* (arXiv:2404.16642), Theorem 3.18 (Kahane's
convexity inequality) and its proof, and of Rhodes–Vargas, *Gaussian multiplicative chaos and
applications: a review* (arXiv:1305.6221), Theorem 2.1.

For `u, u' : ι → H` (the Gram vectors of the two Gaussian vectors, `u i ⊥ u' j`) and
`θ ∈ [0, π/2]`, the interpolating vectors are `U θ i = cos θ • u i + sin θ • u' i`, the
normalised exponentials are `w θ x i = p i e^{⟪U θ i, x⟫ - ⟪U θ i, U θ i⟫ / 2}` and
`W θ x = ∑ i, w θ x i`.  With `x` standard Gaussian, `(⟪U θ i, x⟫)ᵢ` is the Gaussian vector
`cos θ X + sin θ Y` (`X`, `Y` independent).  This file gives the derivatives of `w` in `θ` and
along lines in `x`, and the bounds `w, W, W⁻¹ ≤ M x := A₀ e^{S ‖x‖}` uniformly in `θ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LQGMetric

namespace Kahane

variable {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The interpolating vectors `U θ i = cos θ • u i + sin θ • u' i`. -/
def kU (u u' : ι → H) (θ : ℝ) (i : ι) : H := Real.cos θ • u i + Real.sin θ • u' i

/-- The `θ`-derivative of `kU`. -/
def kU' (u u' : ι → H) (θ : ℝ) (i : ι) : H := (-Real.sin θ) • u i + Real.cos θ • u' i

/-- The normalised exponential `p i e^{⟪U θ i, x⟫ - ⟪U θ i, U θ i⟫ / 2}`. -/
def kw (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (x : H) (i : ι) : ℝ :=
  p i * Real.exp (⟪kU u u' θ i, x⟫ - ⟪kU u u' θ i, kU u u' θ i⟫ / 2)

/-- The total mass `W θ x = ∑ i, w θ x i`. -/
def kW (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (x : H) : ℝ := ∑ i, kw p u u' θ x i

variable {p : ι → ℝ} {u u' : ι → H}

lemma kU_zero (u u' : ι → H) (i : ι) : kU u u' 0 i = u i := by simp [kU]

lemma kU_pi_div_two (u u' : ι → H) (i : ι) : kU u u' (π / 2) i = u' i := by simp [kU]

lemma hasDerivAt_kU (u u' : ι → H) (θ : ℝ) (i : ι) :
    HasDerivAt (fun t => kU u u' t i) (kU' u u' θ i) θ := by
  have h1 := (Real.hasDerivAt_cos θ).smul_const (u i)
  have h2 := (Real.hasDerivAt_sin θ).smul_const (u' i)
  exact h1.add h2

lemma hasDerivAt_kw_theta (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (x : H) (i : ι) :
    HasDerivAt (fun t => kw p u u' t x i)
      (kw p u u' θ x i * (⟪kU' u u' θ i, x⟫ - ⟪kU u u' θ i, kU' u u' θ i⟫)) θ := by
  have hU := hasDerivAt_kU u u' θ i
  have h1 := hU.inner ℝ (hasDerivAt_const θ x)
  have h2 := hU.inner ℝ hU
  have h3 := ((h1.sub (h2.div_const 2)).exp).const_mul (p i)
  refine h3.congr_deriv ?_
  simp only [kw, Pi.sub_apply, inner_zero_right, zero_add]
  rw [real_inner_comm (kU' u u' θ i) (kU u u' θ i)]
  ring

lemma hasDerivAt_kw_line (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (x e : H) (t : ℝ) (i : ι) :
    HasDerivAt (fun s : ℝ => kw p u u' θ (x + s • e) i)
      (kw p u u' θ (x + t • e) i * ⟪kU u u' θ i, e⟫) t := by
  set U := kU u u' θ i
  have hl : HasDerivAt (fun s : ℝ => ⟪U, x + s • e⟫) ⟪U, e⟫ t := by
    have := ((hasDerivAt_id t).mul_const ⟪U, e⟫).const_add ⟪U, x⟫
    refine (this.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp [inner_add_right, real_inner_smul_right]
  have h3 := ((hl.sub_const (⟪U, U⟫ / 2)).exp).const_mul (p i)
  refine h3.congr_deriv ?_
  simp only [kw, U]
  ring

lemma kw_pos (hp : ∀ i, 0 < p i) (θ : ℝ) (x : H) (i : ι) : 0 < kw p u u' θ x i :=
  mul_pos (hp i) (Real.exp_pos _)

lemma kw_le_kW (hp : ∀ i, 0 < p i) (θ : ℝ) (x : H) (i : ι) :
    kw p u u' θ x i ≤ kW p u u' θ x :=
  Finset.single_le_sum (fun j _ => (kw_pos hp θ x j).le) (Finset.mem_univ i)

lemma kW_pos [Nonempty ι] (hp : ∀ i, 0 < p i) (θ : ℝ) (x : H) : 0 < kW p u u' θ x :=
  Finset.sum_pos (fun i _ => kw_pos hp θ x i) Finset.univ_nonempty

lemma continuous_kw (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (i : ι) :
    Continuous fun x => kw p u u' θ x i := by
  unfold kw; fun_prop

lemma continuous_kW (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) :
    Continuous fun x => kW p u u' θ x := by
  unfold kW; exact continuous_finsetSum _ fun i _ => continuous_kw p u u' θ i

/-! ### Uniform bounds -/

/-- `S = ∑ i, (‖u i‖ + ‖u' i‖)` bounds every `‖U θ i‖` and `‖U' θ i‖`. -/
def kS (u u' : ι → H) : ℝ := ∑ i, (‖u i‖ + ‖u' i‖)

lemma kS_nonneg (u u' : ι → H) : 0 ≤ kS u u' :=
  Finset.sum_nonneg fun i _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

lemma norm_le_kS_aux (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (i : ι) :
    ‖a • u i + b • u' i‖ ≤ kS u u' := by
  refine (norm_add_le _ _).trans ((add_le_add ?_ ?_).trans
    (Finset.single_le_sum (f := fun i => ‖u i‖ + ‖u' i‖)
      (fun j _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ i)))
  · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) ha
  · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) hb

lemma norm_kU_le (θ : ℝ) (i : ι) : ‖kU u u' θ i‖ ≤ kS u u' :=
  norm_le_kS_aux _ _ (Real.abs_cos_le_one θ) (Real.abs_sin_le_one θ) i

lemma norm_kU'_le (θ : ℝ) (i : ι) : ‖kU' u u' θ i‖ ≤ kS u u' :=
  norm_le_kS_aux _ _ (by rw [abs_neg]; exact Real.abs_sin_le_one θ) (Real.abs_cos_le_one θ) i

/-- The constant `A₀ = 1 + ∑ p + (∑ p⁻¹) e^{S²/2}`. -/
def kA (p : ι → ℝ) (u u' : ι → H) : ℝ :=
  1 + ∑ i, p i + (∑ i, (p i)⁻¹) * Real.exp (kS u u' ^ 2 / 2)

/-- The dominating function `M x = A₀ e^{S ‖x‖}`. -/
def kM (p : ι → ℝ) (u u' : ι → H) (x : H) : ℝ := kA p u u' * Real.exp (kS u u' * ‖x‖)

lemma one_le_kA (hp : ∀ i, 0 < p i) : 1 ≤ kA p u u' := by
  unfold kA
  have h1 : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => (hp i).le
  have h2 : 0 ≤ (∑ i, (p i)⁻¹) * Real.exp (kS u u' ^ 2 / 2) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => (inv_pos.2 (hp i)).le) (Real.exp_pos _).le
  linarith

lemma one_le_kM (hp : ∀ i, 0 < p i) (x : H) : 1 ≤ kM p u u' x :=
  one_le_mul_of_one_le_of_one_le (one_le_kA hp)
    (Real.one_le_exp (mul_nonneg (kS_nonneg u u') (norm_nonneg x)))

lemma inner_le_kS (θ : ℝ) (i : ι) (x : H) : |⟪kU u u' θ i, x⟫| ≤ kS u u' * ‖x‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_kU_le θ i) (norm_nonneg _))

lemma kW_le_kM (hp : ∀ i, 0 < p i) (θ : ℝ) (x : H) : kW p u u' θ x ≤ kM p u u' x := by
  have h : kW p u u' θ x ≤ (∑ i, p i) * Real.exp (kS u u' * ‖x‖) := by
    unfold kW
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (hp i).le
    have := (le_abs_self _).trans (inner_le_kS (u := u) (u' := u') θ i x)
    have h0 : 0 ≤ ⟪kU u u' θ i, kU u u' θ i⟫ := real_inner_self_nonneg
    linarith
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  unfold kA
  have h2 : 0 ≤ (∑ i, (p i)⁻¹) * Real.exp (kS u u' ^ 2 / 2) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => (inv_pos.2 (hp i)).le) (Real.exp_pos _).le
  linarith

lemma kw_le_kM (hp : ∀ i, 0 < p i) (θ : ℝ) (x : H) (i : ι) : kw p u u' θ x i ≤ kM p u u' x :=
  (kw_le_kW hp θ x i).trans (kW_le_kM hp θ x)

lemma kW_inv_le_kM (hp : ∀ i, 0 < p i) [Nonempty ι] (θ : ℝ) (x : H) :
    (kW p u u' θ x)⁻¹ ≤ kM p u u' x := by
  set i := Classical.arbitrary ι
  refine (inv_anti₀ (kw_pos hp θ x i) (kw_le_kW hp θ x i)).trans ?_
  have e : (kw p u u' θ x i)⁻¹ =
      (p i)⁻¹ * Real.exp (-⟪kU u u' θ i, x⟫ + ⟪kU u u' θ i, kU u u' θ i⟫ / 2) := by
    rw [kw, mul_inv, ← Real.exp_neg]; ring_nf
  rw [e]
  have h1 : -⟪kU u u' θ i, x⟫ + ⟪kU u u' θ i, kU u u' θ i⟫ / 2 ≤
      kS u u' ^ 2 / 2 + kS u u' * ‖x‖ := by
    have ha := (neg_le_abs _).trans (inner_le_kS (u := u) (u' := u') θ i x)
    have hb : ⟪kU u u' θ i, kU u u' θ i⟫ ≤ kS u u' ^ 2 := by
      rw [real_inner_self_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_kU_le θ i) 2
    linarith
  have h2 : (p i)⁻¹ ≤ ∑ j, (p j)⁻¹ :=
    Finset.single_le_sum (f := fun j => (p j)⁻¹) (fun j _ => (inv_pos.2 (hp j)).le)
      (Finset.mem_univ i)
  calc (p i)⁻¹ * Real.exp (-⟪kU u u' θ i, x⟫ + ⟪kU u u' θ i, kU u u' θ i⟫ / 2)
      ≤ (∑ j, (p j)⁻¹) * Real.exp (kS u u' ^ 2 / 2 + kS u u' * ‖x‖) :=
        mul_le_mul h2 (Real.exp_le_exp.2 h1) (Real.exp_pos _).le
          (Finset.sum_nonneg fun j _ => (inv_pos.2 (hp j)).le)
    _ = (∑ j, (p j)⁻¹) * Real.exp (kS u u' ^ 2 / 2) * Real.exp (kS u u' * ‖x‖) := by
        rw [Real.exp_add]; ring
    _ ≤ kM p u u' x := by
        unfold kM kA
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have h1 : 0 ≤ ∑ i, p i := Finset.sum_nonneg fun i _ => (hp i).le
        linarith

/-- `M^m (1 + ‖x‖) ≤ A₀^m e^{(m S + 1) ‖x‖}`. -/
lemma kM_pow_mul_le (hp : ∀ i, 0 < p i) (m : ℕ) (x : H) :
    kM p u u' x ^ m * (1 + ‖x‖) ≤
      kA p u u' ^ m * Real.exp ((m * kS u u' + 1) * ‖x‖) := by
  have hA : 0 ≤ kA p u u' := zero_le_one.trans (one_le_kA hp)
  have h1 : 1 + ‖x‖ ≤ Real.exp ‖x‖ := by
    have := Real.add_one_le_exp ‖x‖; linarith
  unfold kM
  rw [mul_pow, ← Real.exp_nat_mul, add_mul, one_mul, Real.exp_add, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA m)
  rw [show (m : ℝ) * (kS u u' * ‖x‖) = m * kS u u' * ‖x‖ by ring]
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

end Kahane

end LQGMetric

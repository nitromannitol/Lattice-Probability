/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.KahaneBound at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.KahaneCore

/-!
# Kahane's convexity inequality: admissible functions and the integrand bounds

`LQGMetric.Kahane.KahaneFun F F' F'' C k`: `F` is `C²` on `(0, ∞)` with `F'' ≥ 0` there (convex)
and `|F|, |F'|, |F''| ≤ C (y + y⁻¹)^k` on `(0, ∞)`.  This covers `F(y) = y^q` for every real
`q ∉ (0, 1)`, the functions used for the positive and negative moments of Gaussian
multiplicative chaos (Rhodes–Vargas arXiv:1305.6221, Theorems 2.11, 2.12; Berestycki–Powell
arXiv:2404.16642, Theorem 3.18 requires convex `F` of at most polynomial growth).

This file defines the `θ`-derivative `kD` of the interpolation integrand, the functions
`kG i = F'(W) w_i` and their gradients `kGrad i`, which Gaussian integration by parts is applied
to, and bounds all of them by `kUB x ≤ A e^{B ‖x‖}` uniformly in `θ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace NNReal

namespace LQGMetric

namespace Kahane

/-- Admissible convex functions for Kahane's inequality. -/
structure KahaneFun (F F' F'' : ℝ → ℝ) (C : ℝ) (k : ℕ) : Prop where
  hasDerivAt : ∀ y, 0 < y → HasDerivAt F (F' y) y
  hasDerivAt' : ∀ y, 0 < y → HasDerivAt F' (F'' y) y
  continuousOn'' : ContinuousOn F'' (Ioi 0)
  nonneg'' : ∀ y, 0 < y → 0 ≤ F'' y
  growth : ∀ y, 0 < y → |F y| ≤ C * (y + y⁻¹) ^ k
  growth' : ∀ y, 0 < y → |F' y| ≤ C * (y + y⁻¹) ^ k
  growth'' : ∀ y, 0 < y → |F'' y| ≤ C * (y + y⁻¹) ^ k

variable {F F' F'' : ℝ → ℝ} {C : ℝ} {k : ℕ}

lemma KahaneFun.C_nonneg (h : KahaneFun F F' F'' C k) : 0 ≤ C := by
  by_contra hC
  push_neg at hC
  have h1 := (abs_nonneg _).trans (h.growth 1 one_pos)
  have h2 : C * ((1 : ℝ) + 1⁻¹) ^ k < 0 := mul_neg_of_neg_of_pos hC (by positivity)
  linarith

lemma KahaneFun.continuousOn (h : KahaneFun F F' F'' C k) : ContinuousOn F (Ioi 0) :=
  fun y hy => (h.hasDerivAt y hy).continuousAt.continuousWithinAt

lemma KahaneFun.continuousOn' (h : KahaneFun F F' F'' C k) : ContinuousOn F' (Ioi 0) :=
  fun y hy => (h.hasDerivAt' y hy).continuousAt.continuousWithinAt

lemma abs_le_two_mul_pow {f : ℝ → ℝ} (hf : ∀ y, 0 < y → |f y| ≤ C * (y + y⁻¹) ^ k)
    (hC : 0 ≤ C) {y M : ℝ} (hy : 0 < y) (h1 : y ≤ M) (h2 : y⁻¹ ≤ M) :
    |f y| ≤ C * (2 * M) ^ k :=
  (hf y hy).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (add_nonneg hy.le (inv_pos.2 hy).le) (by linarith) k) hC)

variable {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {p : ι → ℝ} {u u' : ι → H}

/-- The `θ`-derivative of `F (W θ x)`. -/
def kD (F' : ℝ → ℝ) (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (x : H) : ℝ :=
  F' (kW p u u' θ x) *
    ∑ i, kw p u u' θ x i * (⟪kU' u u' θ i, x⟫ - ⟪kU u u' θ i, kU' u u' θ i⟫)

/-- `G_i = F'(W) w_i`. -/
def kG (F' : ℝ → ℝ) (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (i : ι) (x : H) : ℝ :=
  F' (kW p u u' θ x) * kw p u u' θ x i

/-- The gradient of `kG i`. -/
def kGrad (F' F'' : ℝ → ℝ) (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (i : ι) (x : H) : H :=
  (F'' (kW p u u' θ x) * kw p u u' θ x i) • ∑ j, kw p u u' θ x j • kU u u' θ j +
    (F' (kW p u u' θ x) * kw p u u' θ x i) • kU u u' θ i

/-- `L x = C (2 M x)^k`, the bound on `F, F', F''` at `W`. -/
def kL (C : ℝ) (k : ℕ) (p : ι → ℝ) (u u' : ι → H) (x : H) : ℝ := C * (2 * kM p u u' x) ^ k

/-- The uniform bound `L (n + 1) M² (S + 1)² (1 + ‖x‖)`. -/
def kUB (C : ℝ) (k : ℕ) (p : ι → ℝ) (u u' : ι → H) (x : H) : ℝ :=
  kL C k p u u' x * (Fintype.card ι + 1) * kM p u u' x ^ 2 * ((kS u u' + 1) ^ 2 * (1 + ‖x‖))

/-- The exponential constants. -/
def kAe (C : ℝ) (k : ℕ) (p : ι → ℝ) (u u' : ι → H) : ℝ :=
  C * 2 ^ k * (Fintype.card ι + 1) * (kS u u' + 1) ^ 2 * kA p u u' ^ (k + 2)

def kBe (k : ℕ) (u u' : ι → H) : ℝ := ((k + 2 : ℕ) * kS u u' + 1)

section bounds

variable (hFK : KahaneFun F F' F'' C k) (hp : ∀ i, 0 < p i)
include hFK hp

lemma kL_nonneg (x : H) : 0 ≤ kL C k p u u' x :=
  mul_nonneg hFK.C_nonneg (pow_nonneg (by linarith [one_le_kM (u := u) (u' := u') hp x]) k)

lemma kUB_le_exp (x : H) :
    kUB C k p u u' x ≤ kAe C k p u u' * Real.exp (kBe k u u' * ‖x‖) := by
  have h := kM_pow_mul_le (u := u) (u' := u') hp (k + 2) x
  have hc : 0 ≤ C * 2 ^ k * (Fintype.card ι + 1) * (kS u u' + 1) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hFK.C_nonneg (by positivity)) (by positivity))
      (by positivity)
  calc kUB C k p u u' x =
        C * 2 ^ k * (Fintype.card ι + 1) * (kS u u' + 1) ^ 2 *
          (kM p u u' x ^ (k + 2) * (1 + ‖x‖)) := by
        unfold kUB kL; rw [mul_pow]; ring
    _ ≤ C * 2 ^ k * (Fintype.card ι + 1) * (kS u u' + 1) ^ 2 *
          (kA p u u' ^ (k + 2) * Real.exp ((((k + 2 : ℕ) : ℝ) * kS u u' + 1) * ‖x‖)) :=
        mul_le_mul_of_nonneg_left h hc
    _ = _ := by unfold kAe kBe; ring

variable [Nonempty ι]

lemma abs_comp_kW_le {f : ℝ → ℝ} (hf : ∀ y, 0 < y → |f y| ≤ C * (y + y⁻¹) ^ k) (θ : ℝ)
    (x : H) : |f (kW p u u' θ x)| ≤ kL C k p u u' x :=
  abs_le_two_mul_pow hf hFK.C_nonneg (kW_pos hp θ x) (kW_le_kM hp θ x) (kW_inv_le_kM hp θ x)

lemma kL_le_kUB (x : H) : kL C k p u u' x ≤ kUB C k p u u' x := by
  have hL := kL_nonneg (u := u) (u' := u') hFK hp x
  have h1 : (1 : ℝ) ≤ Fintype.card ι + 1 := by linarith [(Fintype.card ι).cast_nonneg (α := ℝ)]
  have h2 : 1 ≤ kM p u u' x ^ 2 := one_le_pow₀ (one_le_kM hp x)
  have h3 : 1 ≤ (kS u u' + 1) ^ 2 * (1 + ‖x‖) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [kS_nonneg u u']))
      (by linarith [norm_nonneg x])
  unfold kUB
  calc kL C k p u u' x ≤ kL C k p u u' x * (Fintype.card ι + 1) := le_mul_of_one_le_right hL h1
    _ ≤ kL C k p u u' x * (Fintype.card ι + 1) * kM p u u' x ^ 2 :=
        le_mul_of_one_le_right (mul_nonneg hL (by linarith)) h2
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (mul_nonneg hL (by linarith)) (by linarith)) h3

lemma abs_F_kW_le (θ : ℝ) (x : H) : |F (kW p u u' θ x)| ≤ kUB C k p u u' x :=
  (abs_comp_kW_le hFK hp hFK.growth θ x).trans (kL_le_kUB hFK hp x)

lemma abs_kG_le (θ : ℝ) (i : ι) (x : H) :
    |kG F' p u u' θ i x| ≤ kL C k p u u' x * kM p u u' x := by
  rw [kG, abs_mul, abs_of_pos (kw_pos hp θ x i)]
  exact mul_le_mul (abs_comp_kW_le hFK hp hFK.growth' θ x) (kw_le_kM hp θ x i)
    (kw_pos hp θ x i).le (kL_nonneg hFK hp x)

lemma aux_T_le (x : H) :
    kS u u' * ‖x‖ + kS u u' * kS u u' ≤ (kS u u' + 1) ^ 2 * (1 + ‖x‖) := by
  have hS := kS_nonneg u u'
  have hx := norm_nonneg x
  nlinarith [mul_nonneg hS hx, mul_nonneg (mul_nonneg hS hS) hx]

lemma abs_kG_le_kUB (θ : ℝ) (i : ι) (x : H) : |kG F' p u u' θ i x| ≤ kUB C k p u u' x := by
  refine (abs_kG_le hFK hp θ i x).trans ?_
  have hL := kL_nonneg (u := u) (u' := u') hFK hp x
  have hM := one_le_kM (u := u) (u' := u') hp x
  have h1 : (1 : ℝ) ≤ Fintype.card ι + 1 := by linarith [(Fintype.card ι).cast_nonneg (α := ℝ)]
  have h3 : 1 ≤ (kS u u' + 1) ^ 2 * (1 + ‖x‖) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [kS_nonneg u u']))
      (by linarith [norm_nonneg x])
  unfold kUB
  calc kL C k p u u' x * kM p u u' x ≤ kL C k p u u' x * ((Fintype.card ι + 1) *
        (kM p u u' x ^ 2 * ((kS u u' + 1) ^ 2 * (1 + ‖x‖)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hL
        calc kM p u u' x ≤ 1 * (kM p u u' x ^ 2 * 1) := by
              rw [one_mul, mul_one]; exact le_self_pow₀ hM two_ne_zero
          _ ≤ _ := by gcongr
    _ = _ := by ring

lemma abs_kD_le (θ : ℝ) (x : H) : |kD F' p u u' θ x| ≤ kUB C k p u u' x := by
  have hL := kL_nonneg (u := u) (u' := u') hFK hp x
  have hM := one_le_kM (u := u) (u' := u') hp x
  have hS := kS_nonneg u u'
  set T := kS u u' * ‖x‖ + kS u u' * kS u u'
  have hsum : |∑ i, kw p u u' θ x i * (⟪kU' u u' θ i, x⟫ - ⟪kU u u' θ i, kU' u u' θ i⟫)| ≤
      Fintype.card ι * (kM p u u' x * T) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |kw p u u' θ x i * (⟪kU' u u' θ i, x⟫ - ⟪kU u u' θ i, kU' u u' θ i⟫)|
        ≤ ∑ _i : ι, kM p u u' x * T := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_pos (kw_pos hp θ x i)]
          refine mul_le_mul (kw_le_kM hp θ x i) ((abs_sub _ _).trans (add_le_add ?_ ?_))
            (abs_nonneg _) (by linarith)
          · exact (abs_real_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right (norm_kU'_le θ i) (norm_nonneg _))
          · exact (abs_real_inner_le_norm _ _).trans
              (mul_le_mul (norm_kU_le θ i) (norm_kU'_le θ i) (norm_nonneg _) hS)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hT : T ≤ (kS u u' + 1) ^ 2 * (1 + ‖x‖) := aux_T_le (p := p) hFK hp x
  rw [kD, abs_mul]
  calc |F' (kW p u u' θ x)| * |_| ≤ kL C k p u u' x * (Fintype.card ι * (kM p u u' x * T)) :=
        mul_le_mul (abs_comp_kW_le hFK hp hFK.growth' θ x) hsum (abs_nonneg _) hL
    _ ≤ kL C k p u u' x * ((Fintype.card ι + 1) *
          (kM p u u' x ^ 2 * ((kS u u' + 1) ^ 2 * (1 + ‖x‖)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hL
        have hT0 : 0 ≤ T := by positivity
        gcongr
        · linarith
        · exact le_self_pow₀ hM two_ne_zero
    _ = _ := by unfold kUB; ring

lemma norm_kGrad_le (θ : ℝ) (i : ι) (x : H) :
    ‖kGrad F' F'' p u u' θ i x‖ ≤ kUB C k p u u' x := by
  have hL := kL_nonneg (u := u) (u' := u') hFK hp x
  have hM := one_le_kM (u := u) (u' := u') hp x
  have hS := kS_nonneg u u'
  have hw := kw_pos (u := u) (u' := u') hp θ x i
  have hsum : ‖∑ j, kw p u u' θ x j • kU u u' θ j‖ ≤ Fintype.card ι * (kM p u u' x * kS u u') := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖kw p u u' θ x j • kU u u' θ j‖ ≤ ∑ _j : ι, kM p u u' x * kS u u' :=
          Finset.sum_le_sum fun j _ => by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (kw_pos hp θ x j)]
            exact mul_le_mul (kw_le_kM hp θ x j) (norm_kU_le θ j) (norm_nonneg _) (by linarith)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have h1 : |F'' (kW p u u' θ x) * kw p u u' θ x i| ≤ kL C k p u u' x * kM p u u' x := by
    rw [abs_mul, abs_of_pos hw]
    exact mul_le_mul (abs_comp_kW_le hFK hp hFK.growth'' θ x) (kw_le_kM hp θ x i) hw.le hL
  have h2 : |F' (kW p u u' θ x) * kw p u u' θ x i| ≤ kL C k p u u' x * kM p u u' x :=
    abs_kG_le hFK hp θ i x
  have hLM : 0 ≤ kL C k p u u' x * kM p u u' x := mul_nonneg hL (by linarith)
  have hS2 : kS u u' ≤ (kS u u' + 1) ^ 2 * (1 + ‖x‖) := by
    have := aux_T_le (p := p) (u := u) (u' := u') hFK hp x
    nlinarith [mul_nonneg hS (norm_nonneg x)]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |F'' (kW p u u' θ x) * kw p u u' θ x i| * ‖∑ j, kw p u u' θ x j • kU u u' θ j‖ +
        |F' (kW p u u' θ x) * kw p u u' θ x i| * ‖kU u u' θ i‖
      ≤ kL C k p u u' x * kM p u u' x * (Fintype.card ι * (kM p u u' x * kS u u')) +
        kL C k p u u' x * kM p u u' x * kS u u' :=
        add_le_add (mul_le_mul h1 hsum (norm_nonneg _) hLM)
          (mul_le_mul h2 (norm_kU_le θ i) (norm_nonneg _) hLM)
    _ = kL C k p u u' x * kS u u' * kM p u u' x * (Fintype.card ι * kM p u u' x + 1) := by ring
    _ ≤ kL C k p u u' x * ((kS u u' + 1) ^ 2 * (1 + ‖x‖)) * kM p u u' x *
          ((Fintype.card ι + 1) * kM p u u' x) := by
        have hn := (Fintype.card ι).cast_nonneg (α := ℝ)
        gcongr
        nlinarith
    _ = _ := by unfold kUB; ring

end bounds

end Kahane

end LQGMetric

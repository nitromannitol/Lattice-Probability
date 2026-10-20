/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/KahaneBound.lean.
-/
import LatticeProb.Prob.GaussKahaneCore

/-!
# Kahane's convexity inequality: admissible functions and the integrand bounds

`LatticeProb.Kahane.KahaneFun F F' F'' C k` says that `F` has derivative `F'` on `(0, ∞)`, that
`F'` has derivative `F''` there, that `F'' ≥ 0` on `(0, ∞)` (so `F` is convex there), and that
`|F|, |F'|, |F''| ≤ C (y + y⁻¹) ^ k` on `(0, ∞)`. The namespace `KahaneBoundExample` shows
that this structure is satisfiable.

This file defines the `θ`-derivative `kD` of the interpolation integrand, the functions
`kG i = F'(W) w_i` and their gradients `kGrad i`, to which Gaussian integration by parts is
applied. It proves that `kD`, `kG` and `kGrad` are bounded by `kUB x`, uniformly in `θ`, and
that `kUB x ≤ kAe e^{kBe ‖x‖}`.
-/

noncomputable section

open Set Real
open scoped RealInnerProductSpace

namespace LatticeProb

namespace Kahane

/-- Admissible functions for Kahane's convexity inequality. `KahaneFun F F' F'' C k` says that
`F` has derivative `F'` on `(0, ∞)`, that `F'` has derivative `F''` there, that `F'' ≥ 0` on
`(0, ∞)`, and that `|F|, |F'|, |F''| ≤ C (y + y⁻¹) ^ k` on `(0, ∞)`. -/
structure KahaneFun (F F' F'' : ℝ → ℝ) (C : ℝ) (k : ℕ) : Prop where
  hasDerivAt : ∀ y, 0 < y → HasDerivAt F (F' y) y
  hasDerivAt' : ∀ y, 0 < y → HasDerivAt F' (F'' y) y
  continuousOn'' : ContinuousOn F'' (Ioi 0)
  nonneg'' : ∀ y, 0 < y → 0 ≤ F'' y
  growth : ∀ y, 0 < y → |F y| ≤ C * (y + y⁻¹) ^ k
  growth' : ∀ y, 0 < y → |F' y| ≤ C * (y + y⁻¹) ^ k
  growth'' : ∀ y, 0 < y → |F'' y| ≤ C * (y + y⁻¹) ^ k

variable {F F' F'' : ℝ → ℝ} {C : ℝ} {k : ℕ}

/-- The constant `C` of a `KahaneFun` bound is nonnegative. -/
lemma KahaneFun.C_nonneg (h : KahaneFun F F' F'' C k) : 0 ≤ C := by
  by_contra hC
  have hC' : C < 0 := not_le.1 hC
  have h1 := (abs_nonneg _).trans (h.growth 1 one_pos)
  have h2 : C * ((1 : ℝ) + 1⁻¹) ^ k < 0 := mul_neg_of_neg_of_pos hC' (by positivity)
  linarith

/-- An admissible function `F` is continuous on `(0, ∞)`. -/
lemma KahaneFun.continuousOn (h : KahaneFun F F' F'' C k) : ContinuousOn F (Ioi 0) :=
  fun y hy => (h.hasDerivAt y hy).continuousAt.continuousWithinAt

/-- The derivative `F'` of an admissible function is continuous on `(0, ∞)`. -/
lemma KahaneFun.continuousOn' (h : KahaneFun F F' F'' C k) : ContinuousOn F' (Ioi 0) :=
  fun y hy => (h.hasDerivAt' y hy).continuousAt.continuousWithinAt

/-- If `|f y| ≤ C (y + y⁻¹) ^ k` for all `y > 0` with `C ≥ 0`, and `y ≤ M`, `y⁻¹ ≤ M`,
then `|f y| ≤ C (2 M) ^ k`. -/
lemma abs_le_two_mul_pow {f : ℝ → ℝ} (hf : ∀ y, 0 < y → |f y| ≤ C * (y + y⁻¹) ^ k)
    (hC : 0 ≤ C) {y M : ℝ} (hy : 0 < y) (h1 : y ≤ M) (h2 : y⁻¹ ≤ M) :
    |f y| ≤ C * (2 * M) ^ k :=
  (hf y hy).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (add_nonneg hy.le (inv_pos.2 hy).le) (by linarith) k) hC)

variable {ι : Type*} [Fintype ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {p : ι → ℝ} {u u' : ι → H}

/-- The `θ`-derivative of `F (kW p u u' θ x)`:
`kD F' p u u' θ x = F' (kW p u u' θ x) * ∑ i, kw p u u' θ x i * (⟪kU' u u' θ i, x⟫ -
⟪kU u u' θ i, kU' u u' θ i⟫)`. -/
def kD (F' : ℝ → ℝ) (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (x : H) : ℝ :=
  F' (kW p u u' θ x) *
    ∑ i, kw p u u' θ x i * (⟪kU' u u' θ i, x⟫ - ⟪kU u u' θ i, kU' u u' θ i⟫)

/-- The functions `kG F' p u u' θ i x = F' (kW p u u' θ x) * kw p u u' θ x i`, that is
`G_i = F'(W) w_i` with `W = kW` and `w_i = kw · i`. -/
def kG (F' : ℝ → ℝ) (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (i : ι) (x : H) : ℝ :=
  F' (kW p u u' θ x) * kw p u u' θ x i

/-- The gradient in `x` of `kG F' p u u' θ i`:
`kGrad F' F'' p u u' θ i x = (F'' (kW p u u' θ x) * kw p u u' θ x i) •`
`∑ j, kw p u u' θ x j • kU u u' θ j + (F' (kW p u u' θ x) * kw p u u' θ x i) • kU u u' θ i`. -/
def kGrad (F' F'' : ℝ → ℝ) (p : ι → ℝ) (u u' : ι → H) (θ : ℝ) (i : ι) (x : H) : H :=
  (F'' (kW p u u' θ x) * kw p u u' θ x i) • ∑ j, kw p u u' θ x j • kU u u' θ j +
    (F' (kW p u u' θ x) * kw p u u' θ x i) • kU u u' θ i

/-- The uniform bound constant `kL C k p u u' x = C * (2 * kM p u u' x) ^ k`, a bound for
`F, F', F''` at `kW p u u' θ x` for every `θ`. -/
def kL (C : ℝ) (k : ℕ) (p : ι → ℝ) (u u' : ι → H) (x : H) : ℝ := C * (2 * kM p u u' x) ^ k

/-- The uniform bound `kUB C k p u u' x = kL C k p u u' x * (card ι + 1) * kM p u u' x ^ 2 *
((kS u u' + 1) ^ 2 * (1 + ‖x‖))`. -/
def kUB (C : ℝ) (k : ℕ) (p : ι → ℝ) (u u' : ι → H) (x : H) : ℝ :=
  kL C k p u u' x * (Fintype.card ι + 1) * kM p u u' x ^ 2 * ((kS u u' + 1) ^ 2 * (1 + ‖x‖))

/-- The constant `kAe C k p u u' = C * 2 ^ k * (card ι + 1) * (kS u u' + 1) ^ 2 * kA p u u' ^ (k + 2)`,
in the exponential bound `kUB_le_exp`. -/
def kAe (C : ℝ) (k : ℕ) (p : ι → ℝ) (u u' : ι → H) : ℝ :=
  C * 2 ^ k * (Fintype.card ι + 1) * (kS u u' + 1) ^ 2 * kA p u u' ^ (k + 2)

/-- The exponential rate `kBe k u u' = (k + 2) * kS u u' + 1` in the exponential bound
`kUB_le_exp`. -/
def kBe (k : ℕ) (u u' : ι → H) : ℝ := ((k + 2 : ℕ) * kS u u' + 1)

omit [InnerProductSpace ℝ H] in
/-- The inequality `kS ‖x‖ + kS² ≤ (kS + 1) ^ 2 * (1 + ‖x‖)`, where `kS = kS u u'`. -/
lemma aux_T_le (x : H) :
    kS u u' * ‖x‖ + kS u u' * kS u u' ≤ (kS u u' + 1) ^ 2 * (1 + ‖x‖) := by
  have hS := kS_nonneg u u'
  have hx := norm_nonneg x
  nlinarith [mul_nonneg hS hx, mul_nonneg (mul_nonneg hS hS) hx]

section bounds

variable (hFK : KahaneFun F F' F'' C k) (hp : ∀ i, 0 < p i)
include hFK hp

omit [InnerProductSpace ℝ H] in
/-- The constant `kL C k p u u' x` is nonnegative. -/
lemma kL_nonneg (x : H) : 0 ≤ kL C k p u u' x :=
  mul_nonneg hFK.C_nonneg (pow_nonneg (by linarith [one_le_kM (u := u) (u' := u') hp x]) k)

omit [InnerProductSpace ℝ H] in
/-- The uniform bound satisfies
`kUB C k p u u' x ≤ kAe C k p u u' * exp (kBe k u u' * ‖x‖)`. -/
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

/-- For `f` with the growth bound `|f y| ≤ C (y + y⁻¹) ^ k` on `(0, ∞)`, the value
`|f (kW p u u' θ x)|` is at most `kL C k p u u' x`, for every `θ`. -/
lemma abs_comp_kW_le {f : ℝ → ℝ} (hf : ∀ y, 0 < y → |f y| ≤ C * (y + y⁻¹) ^ k) (θ : ℝ)
    (x : H) : |f (kW p u u' θ x)| ≤ kL C k p u u' x :=
  abs_le_two_mul_pow hf hFK.C_nonneg (kW_pos hp θ x) (kW_le_kM hp θ x) (kW_inv_le_kM hp θ x)

omit [InnerProductSpace ℝ H] [Nonempty ι] in
/-- The constant `kL C k p u u' x` is at most the uniform bound `kUB C k p u u' x`. -/
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

/-- The absolute value of `F (kW p u u' θ x)` is at most `kUB C k p u u' x`, for every `θ`. -/
lemma abs_F_kW_le (θ : ℝ) (x : H) : |F (kW p u u' θ x)| ≤ kUB C k p u u' x :=
  (abs_comp_kW_le hFK hp hFK.growth θ x).trans (kL_le_kUB hFK hp x)

/-- The absolute value of `kG F' p u u' θ i x` is at most `kL C k p u u' x * kM p u u' x`. -/
lemma abs_kG_le (θ : ℝ) (i : ι) (x : H) :
    |kG F' p u u' θ i x| ≤ kL C k p u u' x * kM p u u' x := by
  rw [kG, abs_mul, abs_of_pos (kw_pos hp θ x i)]
  exact mul_le_mul (abs_comp_kW_le hFK hp hFK.growth' θ x) (kw_le_kM hp θ x i)
    (kw_pos hp θ x i).le (kL_nonneg hFK hp x)

/-- The functions `kG F' p u u' θ i` are bounded by `kUB C k p u u' x`, uniformly in `θ`. -/
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

/-- The `θ`-derivative `kD F' p u u' θ x` is bounded by `kUB C k p u u' x`, uniformly in `θ`. -/
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
  have hT : T ≤ (kS u u' + 1) ^ 2 * (1 + ‖x‖) := aux_T_le (u := u) (u' := u') x
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

/-- The gradient `kGrad F' F'' p u u' θ i x` is bounded by `kUB C k p u u' x`, uniformly in
`θ`. -/
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
    have := aux_T_le (u := u) (u' := u') x
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

/-! ### Nonvacuity of `KahaneFun` -/

namespace KahaneBoundExample

/-- For `y > 0`, `2 ≤ y + y⁻¹`. -/
lemma two_le_add_inv {y : ℝ} (hy : 0 < y) : 2 ≤ y + y⁻¹ := by
  have hm : y * y⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
  nlinarith [sq_nonneg (y - 1), inv_pos.2 hy]

-- `y ↦ y ^ 2` with derivative `2 * y`, second derivative `2`, and constants `C = 2`, `k = 2`
-- satisfies `KahaneFun`, so the structure is not empty.
example : KahaneFun (fun y : ℝ => y ^ 2) (fun y => 2 * y) (fun _ => 2) 2 2 where
  hasDerivAt y _ := by simpa using hasDerivAt_pow 2 y
  hasDerivAt' y _ := by simpa using (hasDerivAt_id y).const_mul (2 : ℝ)
  continuousOn'' := continuousOn_const
  nonneg'' _ _ := by norm_num
  growth y hy := by
    have h1 : y ≤ y + y⁻¹ := le_add_of_nonneg_right (inv_pos.2 hy).le
    show |y ^ 2| ≤ 2 * (y + y⁻¹) ^ 2
    rw [abs_of_nonneg (by positivity)]
    nlinarith [pow_le_pow_left₀ hy.le h1 2, sq_nonneg (y + y⁻¹)]
  growth' y hy := by
    have h1 : y ≤ y + y⁻¹ := le_add_of_nonneg_right (inv_pos.2 hy).le
    have h2 := two_le_add_inv hy
    show |2 * y| ≤ 2 * (y + y⁻¹) ^ 2
    rw [abs_of_pos (by linarith)]
    nlinarith
  growth'' y hy := by
    have h2 := two_le_add_inv hy
    show |(2 : ℝ)| ≤ 2 * (y + y⁻¹) ^ 2
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith

end KahaneBoundExample

end Kahane

end LatticeProb

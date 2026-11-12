/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatKernelSquareTheta at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK2
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spectral (cosine) form of the image sums and decay of the Dirichlet kernel
(task P2-DDDFP29, WP-110)

By Poisson summation (mathlib `Complex.tsum_exp_neg_quadratic`, the Jacobi theta
transformation), the image sum of the Gaussian kernel is a cosine series:

  `∑ₙ g_s(c + 2nL) = (2L)⁻¹ ∑ₖ e^{−π²k²s/(2L²)} cos(πkc/L)`   (`HeatSq.tsum_gauss1_shift_eq_cos`),

so the image kernel `q_s(u,v)` is the classical Dirichlet eigenfunction expansion
(Feller II §X.5; Karatzas–Shreve Problem 2.8.8), and it decays like `e^{−π²s/(2L²)}` as
`s → ∞` (`HeatSq.abs_intervalDirKernel_le_exp`). This decay is what makes
`∫_0^∞ p^D_s ds` (the Green function, DDDF `tightness.tex:1517–1523`) and the third term
`η²_t` of DDDF Prop 29 (`tightness.tex:1590–1596`) finite.
-/

noncomputable section

open Real Complex

namespace LQGMetric
namespace HeatSq

/-- **Poisson summation for the image sums.** -/
theorem tsum_gauss1_shift_eq_cos {s L : ℝ} (hs : 0 < s) (hL : 0 < L) (c : ℝ) :
    ∑' n : ℤ, gauss1 s (c + 2 * n * L) = (2 * L)⁻¹ *
      ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) * Real.cos (π * k * c / L) := by
  set A : ℝ := 2 * L ^ 2 / (π * s) with hAdef
  set B : ℝ := -(c * L / (π * s)) with hBdef
  have hA : 0 < A := by positivity
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hP := Complex.tsum_exp_neg_quadratic (a := (A : ℂ)) (by simpa using hA) (B : ℂ)
  -- the left side
  have hl : ∀ n : ℤ, cexp (-(π : ℂ) * (A : ℂ) * (n : ℂ) ^ 2 + 2 * (π : ℂ) * (B : ℂ) * (n : ℂ)) =
      ((Real.exp (c ^ 2 / (2 * s)) * Real.exp (-(c + 2 * n * L) ^ 2 / (2 * s)) : ℝ) : ℂ) := by
    intro n
    rw [← Real.exp_add, Complex.ofReal_exp]; congr 1
    simp only [hAdef, hBdef]; push_cast; field_simp; ring
  simp_rw [hl] at hP
  rw [← Complex.ofReal_tsum, tsum_mul_left] at hP
  -- the right side, term by term
  have hr : ∀ k : ℤ, (cexp (-(π : ℂ) / (A : ℂ) * ((k : ℂ) + I * (B : ℂ)) ^ 2)).re =
      Real.exp (c ^ 2 / (2 * s)) *
        (Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) * Real.cos (π * k * c / L)) := by
    intro k
    have e : -(π : ℂ) / (A : ℂ) * ((k : ℂ) + I * (B : ℂ)) ^ 2 =
        ((-π / A * (k ^ 2 - B ^ 2) : ℝ) : ℂ) + ((-π / A * (2 * k * B) : ℝ) : ℂ) * I := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [e, Complex.exp_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, add_zero,
      mul_one, zero_add]
    rw [show ∀ x y z : ℝ, Real.exp x * (Real.exp y * z) = Real.exp (x + y) * z from
      fun x y z => by rw [Real.exp_add]; ring]
    congr 1
    · congr 1; simp only [hAdef, hBdef]; field_simp; ring
    · congr 1; simp only [hAdef, hBdef]; field_simp
  -- positivity of the left side forces summability of the right side
  set X := ∑' n : ℤ, Real.exp (-(c + 2 * n * L) ^ 2 / (2 * s))
  have hXs : Summable (fun n : ℤ => Real.exp (-(c + 2 * n * L) ^ 2 / (2 * s))) := by
    have := (summable_gauss1_shift hs hL c).mul_left (Real.sqrt (2 * π * s))
    refine this.congr fun n => ?_
    unfold gauss1
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have hX : 0 < X := hXs.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  set T := ∑' k : ℤ, cexp (-(π : ℂ) / (A : ℂ) * ((k : ℂ) + I * (B : ℂ)) ^ 2)
  have hT : Summable (fun k : ℤ => cexp (-(π : ℂ) / (A : ℂ) * ((k : ℂ) + I * (B : ℂ)) ^ 2)) := by
    by_contra hns
    have h0 : T = 0 := tsum_eq_zero_of_not_summable hns
    rw [h0, mul_zero, Complex.ofReal_eq_zero] at hP
    exact (mul_pos (Real.exp_pos _) hX).ne' hP
  have hcpow : (1 : ℂ) / (A : ℂ) ^ (1 / 2 : ℂ) = (((Real.sqrt A)⁻¹ : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_inv, Complex.ofReal_cpow hA.le, one_div]
    push_cast; rfl
  rw [hcpow] at hP
  have hre := congrArg Complex.re hP
  rw [Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_tsum hT] at hre
  simp_rw [hr] at hre
  rw [tsum_mul_left] at hre
  -- conclude
  have hX' : ∑' n : ℤ, gauss1 s (c + 2 * n * L) = (Real.sqrt (2 * π * s))⁻¹ * X := by
    unfold gauss1; rw [tsum_mul_left]
  rw [hX']
  have hE := Real.exp_pos (c ^ 2 / (2 * s))
  have hsq : (Real.sqrt (2 * π * s))⁻¹ * (Real.sqrt A)⁻¹ = (2 * L)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [show 2 * π * s * A = (2 * L) ^ 2 by simp only [hAdef]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hX2 : X = (Real.sqrt A)⁻¹ * ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) *
      Real.cos (π * k * c / L) := by
    have := hre
    rw [← mul_assoc, mul_comm (Real.sqrt A)⁻¹, mul_assoc] at this
    exact mul_left_cancel₀ hE.ne' this
  rw [hX2, ← mul_assoc, hsq]

lemma natAbs_le_sq (k : ℤ) : (k.natAbs : ℝ) ≤ (k : ℝ) ^ 2 := by
  have e : (k : ℝ) ^ 2 = (k.natAbs : ℝ) ^ 2 := by rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [e]
  rcases Nat.eq_zero_or_pos k.natAbs with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ k.natAbs := by exact_mod_cast h
    nlinarith

lemma summable_exp_neg_mul_int_sq' {l : ℝ} (hl : 0 < l) :
    Summable (fun k : ℤ => Real.exp (-l * k ^ 2)) := by
  have hr1 : Real.exp (-l) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun k => ?_)
    (summable_geom_natAbs (Real.exp_pos _).le hr1)
  rw [← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by nlinarith [natAbs_le_sq k])

/-- The constant of the large-time decay bound (times `s ≥ s₀`). -/
def decayConst (L s₀ : ℝ) : ℝ :=
  L⁻¹ * Real.exp (π ^ 2 / (2 * L ^ 2) * s₀) *
    ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀)) ^ k.natAbs

lemma exp_neg_mul_sq_le {l s : ℝ} (hl0 : 0 < l) (hs : 1 ≤ s) {k : ℤ} (hk : k ≠ 0) :
    Real.exp (-l * s * k ^ 2) ≤ Real.exp l * Real.exp (-l * s) * Real.exp (-l) ^ k.natAbs := by
  have hk1 : (1 : ℝ) ≤ k.natAbs := Nat.one_le_cast.mpr (Int.natAbs_pos.mpr hk)
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : 0 ≤ ((k.natAbs : ℝ) - 1) * (s * ((k.natAbs : ℝ) + 1) - 1) :=
    mul_nonneg (by linarith) (by nlinarith)
  have h2 : (k : ℝ) ^ 2 = (k.natAbs : ℝ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [h2]
  nlinarith [mul_nonneg hl0.le h1]

lemma abs_cos_sub_cos_term_le {l s : ℝ} (hl0 : 0 < l) (hs : 1 ≤ s) (α β : ℝ) (k : ℤ) :
    |Real.exp (-l * s * k ^ 2) * Real.cos (k * α) - Real.exp (-l * s * k ^ 2) * Real.cos (k * β)|
      ≤ 2 * Real.exp l * Real.exp (-l * s) * Real.exp (-l) ^ k.natAbs := by
  by_cases hk : k = 0
  · subst hk; simp only [Int.cast_zero, zero_mul, Real.cos_zero, sub_self, abs_zero]; positivity
  rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hc : |Real.cos (k * α) - Real.cos (k * β)| ≤ 2 := by
    have := abs_sub (Real.cos (k * α)) (Real.cos (k * β))
    linarith [Real.abs_cos_le_one (k * α), Real.abs_cos_le_one (k * β)]
  calc Real.exp (-l * s * k ^ 2) * |Real.cos (k * α) - Real.cos (k * β)|
      ≤ (Real.exp l * Real.exp (-l * s) * Real.exp (-l) ^ k.natAbs) * 2 :=
        mul_le_mul (exp_neg_mul_sq_le hl0 hs hk) hc (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The time rescaling `e^{−l s k²} = e^{−(l s₀)(s/s₀) k²}`. -/
lemma exp_rescale (l s s₀ : ℝ) (hs₀ : 0 < s₀) (k : ℤ) :
    Real.exp (-l * s * k ^ 2) = Real.exp (-(l * s₀) * (s / s₀) * k ^ 2) := by
  congr 1; field_simp

/-- **Large-time decay of the image kernel**: for `0 < s₀ ≤ s`,
`|q_s(u,v)| ≤ C(L,s₀) e^{−π²s/(2L²)}`. -/
theorem abs_intervalDirKernel_le_exp {a L s s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (u v : ℝ) :
    |intervalDirKernel a L s u v| ≤ decayConst L s₀ * Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s) := by
  have hl0 : 0 < π ^ 2 / (2 * L ^ 2) := by positivity
  have hl0' : 0 < π ^ 2 / (2 * L ^ 2) * s₀ := by positivity
  have hs1 : 1 ≤ s / s₀ := (one_le_div hs₀).mpr hs
  have hs0 : 0 < s := hs₀.trans_le hs
  have hr01 : Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hG : Summable (fun k : ℤ => Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2)) := by
    have := summable_exp_neg_mul_int_sq' (l := π ^ 2 / (2 * L ^ 2) * s) (by positivity)
    refine this.congr fun k => ?_
    ring_nf
  have hcos : ∀ α : ℝ, Summable (fun k : ℤ =>
      Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) * Real.cos (k * α)) :=
    fun α => Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)) hG)
  have hcosEq : ∀ c : ℝ, ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) *
      Real.cos (π * k * c / L) = ∑' k : ℤ, Real.exp (-(π ^ 2 / (2 * L ^ 2)) * s * k ^ 2) *
      Real.cos (k * (π * c / L)) := fun c => by
    congr 1; funext k; congr 2; ring
  rw [intervalDirKernel_eq_sub hs0 hL, tsum_gauss1_shift_eq_cos hs0 hL,
    tsum_gauss1_shift_eq_cos hs0 hL, hcosEq, hcosEq, ← mul_sub,
    ← (hcos _).tsum_sub (hcos _)]
  have hh := (summable_geom_natAbs (Real.exp_pos _).le hr01).mul_left
    (2 * Real.exp (π ^ 2 / (2 * L ^ 2) * s₀) *
      Real.exp (-(π ^ 2 / (2 * L ^ 2) * s₀) * (s / s₀)))
  have hd := (hcos (π * (u - v) / L)).sub (hcos (π * (u + v - 2 * a) / L))
  have hb := (norm_tsum_le_tsum_norm hd.norm).trans (hd.norm.tsum_le_tsum
    (fun k => by
      rw [Real.norm_eq_abs, exp_rescale _ s s₀ hs₀ k]
      exact (abs_cos_sub_cos_term_le hl0' hs1 _ _ k).trans_eq (by ring)) hh)
  rw [Real.norm_eq_abs, tsum_mul_left] at hb
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * L)⁻¹)]
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_
  have e : -(π ^ 2 / (2 * L ^ 2) * s₀) * (s / s₀) = -(π ^ 2 / (2 * L ^ 2)) * s := by
    field_simp
  rw [e]
  unfold decayConst
  field_simp

end HeatSq
end LQGMetric

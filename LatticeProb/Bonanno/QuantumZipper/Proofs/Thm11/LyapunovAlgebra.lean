/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm11.LyapunovAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Theorem 1.1 blueprint nodes FD-7 and FD-8

FD-7: the algebraic identities of the generator `L = (2/z)·∇ + (κ/2)∂ₓ²` of the one-point
motion `dZ = (2/Z)dt − √κ dB`, written in real coordinates `z = x + iy`, `r² = x² + y²`,
with the partial derivatives of the test functions supplied explicitly; and the
`1/δ`-Lipschitz property of `arg` on `{Im ≥ δ}`.

FD-8: the function `g` on `(0,π)` with `g(π/2) = 0`,
`g'(θ) = −(8/κ) sin^a θ ∫_{π/2}^θ sin^{−a}`, `a = 8/κ − 2`: smoothness, the ODE
`(κ/2) sin²θ g'' + (κ−4) sinθ cosθ g' = −4 sin²θ`, and bounds on `g, g'` for `0 < κ ≤ 4`.
Finally `LV = −(4−κ)/(2r²)` for `V(z) = −log|z| + ((4−κ)/4) g(arg z)`.
-/

noncomputable section

open Real MeasureTheory Set intervalIntegral

namespace QuantumZipper

namespace Thm11Lyap

/-! ## FD-7: generator algebra -/

/-! ### `arg` is `1/δ`-Lipschitz on `{Im ≥ δ}` -/

theorem arg_eq_pi_div_two_sub_arctan {z : ℂ} (hz : 0 < z.im) :
    Complex.arg z = π / 2 - arctan (z.re / z.im) := by
  set u := z.re / z.im
  have h1 : 0 < √(1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hn : ‖z‖ = z.im * √(1 + u ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply,
      show z.re * z.re + z.im * z.im = z.im ^ 2 * (1 + u ^ 2) by simp only [u]; field_simp; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hz.le]
  have hθ : π / 2 - arctan u ∈ Ioc (-π) π := by
    constructor <;> linarith [arctan_lt_pi_div_two u, neg_pi_div_two_lt_arctan u, pi_pos]
  have hzeq : z = (‖z‖ : ℂ) * (Complex.cos (π / 2 - arctan u : ℝ)
      + Complex.sin (π / 2 - arctan u : ℝ) * Complex.I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two_sub,
      Real.sin_pi_div_two_sub, sin_arctan, cos_arctan, hn]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
      simp only [u]; field_simp; ring
    · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
      field_simp; ring
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  conv_lhs => rw [hzeq]
  exact Complex.arg_mul_cos_add_sin_mul_I hzn hθ

theorem arg_lipschitz_of_im_ge {δ : ℝ} (hδ : 0 < δ) {z w : ℂ} (hz : δ ≤ z.im) (hw : δ ≤ w.im) :
    |Complex.arg z - Complex.arg w| ≤ ‖z - w‖ / δ := by
  set a := (z - w).re
  set b := (z - w).im
  let X : ℝ → ℝ := fun t => w.re + t * a
  let Y : ℝ → ℝ := fun t => w.im + t * b
  have hY : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ Y t := by
    intro t ht
    have : Y t = (1 - t) * w.im + t * z.im := by simp only [Y, b, Complex.sub_im]; ring
    rw [this]; nlinarith [ht.1, ht.2]
  let φ : ℝ → ℝ := fun t => π / 2 - arctan (X t / Y t)
  let φ' : ℝ → ℝ := fun t => -((a * Y t - X t * b) / (X t ^ 2 + Y t ^ 2))
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' t) (Icc 0 1) t := by
    intro t ht
    have hYt : 0 < Y t := lt_of_lt_of_le hδ (hY t ht)
    have hX : HasDerivAt X a t := by
      show HasDerivAt (fun t => w.re + t * a) a t
      simpa using ((hasDerivAt_id t).mul_const a).const_add w.re
    have hYd : HasDerivAt Y b t := by
      show HasDerivAt (fun t => w.im + t * b) b t
      simpa using ((hasDerivAt_id t).mul_const b).const_add w.im
    have hq := (hX.div hYd hYt.ne')
    have h := ((hasDerivAt_arctan (X t / Y t)).comp t hq).const_sub (π / 2)
    have h' : HasDerivAt φ _ t := h
    refine (h'.congr_deriv ?_).hasDerivWithinAt
    show _ = -((a * Y t - X t * b) / (X t ^ 2 + Y t ^ 2))
    field_simp
    ring
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖φ' t‖ ≤ ‖z - w‖ / δ := by
    intro t ht
    have hYt : δ ≤ Y t := hY t (Ico_subset_Icc_self ht)
    have hYp : 0 < Y t := lt_of_lt_of_le hδ hYt
    have hr : 0 < X t ^ 2 + Y t ^ 2 := by positivity
    have hn : ‖z - w‖ = √(a ^ 2 + b ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_apply]; simp only [a, b]; ring_nf
    set R := √(X t ^ 2 + Y t ^ 2)
    have hRp : 0 < R := Real.sqrt_pos.2 hr
    have hR2 : R ^ 2 = X t ^ 2 + Y t ^ 2 := Real.sq_sqrt hr.le
    have hYR : δ ≤ R := by
      calc δ ≤ Y t := hYt
        _ = √(Y t ^ 2) := (Real.sqrt_sq hYp.le).symm
        _ ≤ R := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (X t)])
    set N := √(a ^ 2 + b ^ 2)
    have hN0 : 0 ≤ N := Real.sqrt_nonneg _
    have hN2 : N ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
    -- |aY − Xb| ≤ N R
    have hcs : |a * Y t - X t * b| ≤ N * R := by
      have hsq : (a * Y t - X t * b) ^ 2 ≤ (N * R) ^ 2 := by
        rw [mul_pow, hN2, hR2]; nlinarith [sq_nonneg (a * X t + b * Y t)]
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (by positivity : 0 ≤ N * R)]
      exact Real.sqrt_le_sqrt hsq
    rw [Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos hr, hn, ← hR2, div_le_div_iff₀ (by positivity) hδ]
    calc |a * Y t - X t * b| * δ ≤ N * R * δ := by gcongr
      _ ≤ N * R * R := by gcongr
      _ = N * R ^ 2 := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound 1 (by simp)
  have hφ1 : φ 1 = Complex.arg z := by
    rw [arg_eq_pi_div_two_sub_arctan (lt_of_lt_of_le hδ hz)]
    simp [φ, X, Y, a, b]
  have hφ0 : φ 0 = Complex.arg w := by
    rw [arg_eq_pi_div_two_sub_arctan (lt_of_lt_of_le hδ hw)]
    simp [φ, X, Y]
  rw [hφ1, hφ0, Real.norm_eq_abs] at key
  simpa using key

/-! ## FD-8: the function `g` -/

/-- The exponent `a = 8/κ − 2`. -/
def gExp (κ : ℝ) : ℝ := 8 / κ - 2

/-- `I(θ) = ∫_{π/2}^θ sin^{−a} φ dφ`. -/
def gInt (κ θ : ℝ) : ℝ := ∫ φ in π / 2..θ, sin φ ^ (-gExp κ)

/-- `g'(θ) = −(8/κ) sin^a θ · I(θ)`. -/
def gPrime (κ θ : ℝ) : ℝ := -(8 / κ) * sin θ ^ gExp κ * gInt κ θ

/-- `g(θ) = ∫_{π/2}^θ g'`. -/
def gFun (κ θ : ℝ) : ℝ := ∫ t in π / 2..θ, gPrime κ t

theorem sin_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Ioo 0 π) : 0 < sin θ := sin_pos_of_pos_of_lt_pi h.1 h.2

theorem pi_div_two_mem_Ioo : π / 2 ∈ Ioo 0 π := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩

theorem uIcc_subset_Ioo {θ : ℝ} (h : θ ∈ Ioo 0 π) : uIcc (π / 2) θ ⊆ Ioo 0 π :=
  Set.ordConnected_Ioo.uIcc_subset pi_div_two_mem_Ioo h

theorem hasDerivAt_primitive {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo 0 π)) {θ : ℝ}
    (h : θ ∈ Ioo 0 π) : HasDerivAt (fun u => ∫ x in π / 2..u, f x) (f θ) θ :=
  integral_hasDerivAt_right ((hf.mono (uIcc_subset_Ioo h)).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter isOpen_Ioo θ h) (hf.continuousAt (isOpen_Ioo.mem_nhds h))

theorem contDiffOn_primitive {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo 0 π)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => ∫ x in π / 2..u, f x) (Ioo 0 π) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun θ h => (hasDerivAt_primitive hf.continuousOn h).differentiableAt.differentiableWithinAt, ?_⟩
  exact hf.congr fun θ h => (hasDerivAt_primitive hf.continuousOn h).deriv

theorem contDiffOn_sin_rpow (p : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ => sin θ ^ p) (Ioo 0 π) :=
  contDiff_sin.contDiffOn.rpow_const_of_ne fun _ h => (sin_pos_of_mem_Ioo h).ne'

theorem contDiffOn_gInt (κ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gInt κ) (Ioo 0 π) :=
  contDiffOn_primitive (contDiffOn_sin_rpow _)

theorem contDiffOn_gPrime (κ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gPrime κ) (Ioo 0 π) :=
  (contDiffOn_const.mul (contDiffOn_sin_rpow _)).mul (contDiffOn_gInt κ)

/-- FD-8: smoothness of `g` on `(0,π)`. -/
theorem contDiffOn_gFun (κ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gFun κ) (Ioo 0 π) :=
  contDiffOn_primitive (contDiffOn_gPrime κ)

theorem hasDerivAt_gFun (κ : ℝ) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    HasDerivAt (gFun κ) (gPrime κ θ) θ :=
  hasDerivAt_primitive (contDiffOn_gPrime κ).continuousOn h

/-- The derivative of `g'`. -/
theorem hasDerivAt_gPrime (κ : ℝ) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    HasDerivAt (gPrime κ)
      (-(8 / κ) * (cos θ * gExp κ * sin θ ^ (gExp κ - 1) * gInt κ θ + sin θ ^ gExp κ * sin θ ^ (-gExp κ)))
      θ := by
  have hs := sin_pos_of_mem_Ioo h
  have h1 := (hasDerivAt_sin θ).rpow_const (p := gExp κ) (Or.inl hs.ne')
  have h2 : HasDerivAt (gInt κ) (sin θ ^ (-gExp κ)) θ :=
    hasDerivAt_primitive (contDiffOn_sin_rpow _).continuousOn h
  have e : gPrime κ = fun y => -(8 / κ) * ((fun y => sin y ^ gExp κ) * gInt κ) y := by
    funext y; simp [gPrime, mul_assoc]
  rw [e]
  exact (h1.mul h2).const_mul (-(8 / κ))

/-- FD-8: the ODE `(κ/2) sin²θ g'' + (κ−4) sinθ cosθ g' = −4 sin²θ` on `(0,π)`. -/
theorem gFun_ode {κ : ℝ} (hκ : κ ≠ 0) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    κ / 2 * sin θ ^ 2 * deriv (gPrime κ) θ + (κ - 4) * sin θ * cos θ * gPrime κ θ
      = -4 * sin θ ^ 2 := by
  have hs := sin_pos_of_mem_Ioo h
  rw [(hasDerivAt_gPrime κ h).deriv]
  have e1 : sin θ ^ gExp κ * sin θ ^ (-gExp κ) = 1 := by
    rw [Real.rpow_neg hs.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs _).ne']
  have e2 : sin θ ^ (gExp κ - 1) = sin θ ^ gExp κ / sin θ := by
    rw [Real.rpow_sub_one hs.ne']
  rw [e1, e2]
  simp only [gPrime, gExp]
  field_simp
  ring

/-- For `0 < κ ≤ 4` (so `a ≥ 0`): `|sin^a θ · I(θ)| ≤ |θ − π/2|`. -/
theorem abs_sin_rpow_mul_gInt_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    |sin θ ^ gExp κ * gInt κ θ| ≤ |θ - π / 2| := by
  have hs := sin_pos_of_mem_Ioo h
  have ha : 0 ≤ gExp κ := by
    unfold gExp; rw [sub_nonneg, le_div_iff₀ hκ]; linarith
  have hbd : ∀ φ ∈ Set.uIoc (π / 2) θ, ‖sin φ ^ (-gExp κ)‖ ≤ sin θ ^ (-gExp κ) := by
    intro φ hφ
    have hφI : φ ∈ Ioo 0 π := uIcc_subset_Ioo h (uIoc_subset_uIcc hφ)
    have hsφ := sin_pos_of_mem_Ioo hφI
    have hle : sin θ ≤ sin φ := by
      rcases le_or_gt θ (π / 2) with hθ | hθ
      · rw [uIoc_of_ge hθ] at hφ
        exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [h.1, pi_pos]) hφ.2 hφ.1.le
      · rw [uIoc_of_le hθ.le] at hφ
        rw [← sin_pi_sub θ, ← sin_pi_sub φ]
        exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [hφ.2, h.2, pi_pos])
          (by linarith [hφ.1]) (by linarith [hφ.2])
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hsφ _)]
    exact Real.rpow_le_rpow_of_nonpos hs hle (by linarith)
  have hI := norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs] at hI
  have hsa : 0 < sin θ ^ gExp κ := Real.rpow_pos_of_pos hs _
  rw [abs_mul, abs_of_pos hsa]
  calc sin θ ^ gExp κ * |gInt κ θ| ≤ sin θ ^ gExp κ * (sin θ ^ (-gExp κ) * |θ - π / 2|) := by
        gcongr; exact hI
    _ = |θ - π / 2| := by
        rw [← mul_assoc, Real.rpow_neg hs.le, mul_inv_cancel₀ hsa.ne', one_mul]

theorem abs_sub_pi_div_two_le {θ : ℝ} (h : θ ∈ Ioo 0 π) : |θ - π / 2| ≤ π / 2 := by
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-- FD-8: `|g'| ≤ 4π/κ` on `(0,π)` for `0 < κ ≤ 4`. -/
theorem abs_gPrime_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    |gPrime κ θ| ≤ 4 * π / κ := by
  have e : gPrime κ θ = -(8 / κ) * (sin θ ^ gExp κ * gInt κ θ) := by
    simp only [gPrime]; ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by positivity)]
  calc 8 / κ * |sin θ ^ gExp κ * gInt κ θ| ≤ 8 / κ * (π / 2) := by
        gcongr
        exact (abs_sin_rpow_mul_gInt_le hκ hκ4 h).trans (abs_sub_pi_div_two_le h)
    _ = 4 * π / κ := by ring

/-- FD-8: `|g| ≤ 2π²/κ` on `(0,π)` for `0 < κ ≤ 4`. -/
theorem abs_gFun_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {θ : ℝ} (h : θ ∈ Ioo 0 π) :
    |gFun κ θ| ≤ 2 * π ^ 2 / κ := by
  have hbd : ∀ t ∈ Set.uIoc (π / 2) θ, ‖gPrime κ t‖ ≤ 4 * π / κ := fun t ht =>
    abs_gPrime_le hκ hκ4 (uIcc_subset_Ioo h (uIoc_subset_uIcc ht))
  have hI := norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs] at hI
  calc |gFun κ θ| ≤ 4 * π / κ * |θ - π / 2| := hI
    _ ≤ 4 * π / κ * (π / 2) := by gcongr; exact abs_sub_pi_div_two_le h
    _ = 2 * π ^ 2 / κ := by ring


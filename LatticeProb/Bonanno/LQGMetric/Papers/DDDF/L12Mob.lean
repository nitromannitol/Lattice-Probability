/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L12Mob at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DDDF Lemma 12′, node S12b: the Möbius automorphisms of the disc

Decision D-B4 (`decisions/DEC-B.md` §(d)): the maps of DDDF Lemma 12′ are
`affine ∘ G ∘ M ∘ G⁻¹ ∘ affine` with `M` a Möbius automorphism of a disc moving two small boundary
arcs next to the two "ends" `−ρ`, `ρ`. We use the explicit family
`mob β κ z = (cos β · e^{iκ} z − i sin β) / (cos β + i sin β · e^{iκ} z)`
(rotation by `κ`, then the hyperbolic automorphism of the disc preserving the imaginary axis),
for `|sin β| < cos β`. It maps the closed disc into itself, is Lipschitz on it with constant
`2/(cos β − |sin β|)`, sends `e^{i(2β−κ)} ↦ 1` and `e^{i(π−2β−κ)} ↦ −1`. Own elementary
computation (standard Möbius algebra), recorded under D-DDDF-14.
-/

namespace LQGMetric.DDDF.L12

open Set Real

/-- The Möbius automorphism of the unit disc used in Lemma 12′. -/
noncomputable def mob (β κ : ℝ) (z : ℂ) : ℂ :=
  ((Real.cos β : ℂ) * Complex.exp (κ * Complex.I) * z - (Real.sin β : ℂ) * Complex.I) /
    ((Real.cos β : ℂ) + (Real.sin β : ℂ) * Complex.I * Complex.exp (κ * Complex.I) * z)

/-- Its denominator. -/
noncomputable def mobDen (β κ : ℝ) (z : ℂ) : ℂ :=
  (Real.cos β : ℂ) + (Real.sin β : ℂ) * Complex.I * Complex.exp (κ * Complex.I) * z

lemma norm_exp_mul_I (κ : ℝ) : ‖Complex.exp (κ * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I κ

lemma norm_mobDen_ge {β κ : ℝ} (hβ : |Real.sin β| < Real.cos β) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Real.cos β - |Real.sin β| ≤ ‖mobDen β κ z‖ := by
  have h1 := norm_sub_norm_le ((Real.cos β : ℂ)) (-((Real.sin β : ℂ) * Complex.I *
    Complex.exp (κ * Complex.I) * z))
  have hc0 : 0 ≤ Real.cos β := by linarith [abs_nonneg (Real.sin β)]
  rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc0, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    norm_exp_mul_I, Real.norm_eq_abs] at h1
  unfold mobDen
  nlinarith [abs_nonneg (Real.sin β)]

lemma mobDen_ne {β κ : ℝ} (hβ : |Real.sin β| < Real.cos β) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    mobDen β κ z ≠ 0 := by
  intro h
  have := norm_mobDen_ge (κ := κ) hβ hz
  rw [h, norm_zero] at this; linarith

lemma mob_eq (β κ : ℝ) (z : ℂ) : mob β κ z =
    ((Real.cos β : ℂ) * Complex.exp (κ * Complex.I) * z - (Real.sin β : ℂ) * Complex.I) /
      mobDen β κ z := rfl

/-- `mob` maps the closed unit disc into itself. -/
theorem norm_mob_le_one {β κ : ℝ} (hβ : |Real.sin β| < Real.cos β) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖mob β κ z‖ ≤ 1 := by
  set x := Complex.exp (κ * Complex.I) * z with hx
  have hxn : ‖x‖ ≤ 1 := by rw [hx, norm_mul, norm_exp_mul_I, one_mul]; exact hz
  have hx2 : x.re * x.re + x.im * x.im ≤ 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg x]
  have hcs : Real.sin β ^ 2 ≤ Real.cos β ^ 2 := by
    rw [← sq_abs (Real.sin β)]; nlinarith [abs_nonneg (Real.sin β)]
  have hnum : (Real.cos β : ℂ) * Complex.exp (κ * Complex.I) * z - (Real.sin β : ℂ) * Complex.I
      = (Real.cos β : ℂ) * x - (Real.sin β : ℂ) * Complex.I := by rw [hx]; ring
  have hden : mobDen β κ z = (Real.cos β : ℂ) + (Real.sin β : ℂ) * Complex.I * x := by
    rw [hx, mobDen]; ring
  have hsq : Complex.normSq ((Real.cos β : ℂ) * x - (Real.sin β : ℂ) * Complex.I) ≤
      Complex.normSq ((Real.cos β : ℂ) + (Real.sin β : ℂ) * Complex.I * x) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    nlinarith [mul_nonneg (sub_nonneg.2 hcs) (sub_nonneg.2 hx2)]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
  rw [mob_eq, hnum, hden, norm_div]
  apply div_le_one_of_le₀ _ (norm_nonneg _)
  nlinarith [norm_nonneg ((Real.cos β : ℂ) * x - (Real.sin β : ℂ) * Complex.I),
    norm_nonneg ((Real.cos β : ℂ) + (Real.sin β : ℂ) * Complex.I * x)]

/-- The Möbius difference formula. -/
theorem mob_sub {β κ : ℝ} {z z' : ℂ} (hz : mobDen β κ z ≠ 0) (hz' : mobDen β κ z' ≠ 0) :
    mob β κ z - mob β κ z' = ((Real.cos β : ℂ) ^ 2 - (Real.sin β : ℂ) ^ 2) *
      Complex.exp (κ * Complex.I) * (z - z') / (mobDen β κ z * mobDen β κ z') := by
  rw [mob_eq, mob_eq, div_sub_div _ _ hz hz']
  congr 1
  simp only [mobDen]
  linear_combination ((Real.sin β : ℂ) ^ 2 * Complex.exp (κ * Complex.I) * (z - z')) *
    Complex.I_sq

/-- Lipschitz bound on the closed unit disc. -/
theorem norm_mob_sub_le {β κ : ℝ} (hβ : |Real.sin β| < Real.cos β) {z z' : ℂ} (hz : ‖z‖ ≤ 1)
    (hz' : ‖z'‖ ≤ 1) :
    ‖mob β κ z - mob β κ z'‖ ≤ 2 / (Real.cos β - |Real.sin β|) * ‖z - z'‖ := by
  set m := Real.cos β - |Real.sin β| with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have h1 := norm_mobDen_ge (κ := κ) hβ hz
  have h2 := norm_mobDen_ge (κ := κ) hβ hz'
  rw [mob_sub (mobDen_ne hβ hz) (mobDen_ne hβ hz'), norm_div, norm_mul, norm_mul, norm_mul,
    norm_exp_mul_I, mul_one]
  have hc2 : ‖(Real.cos β : ℂ) ^ 2 - (Real.sin β : ℂ) ^ 2‖ = m * (Real.cos β + |Real.sin β|) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    · rw [hm, ← sq_abs (Real.sin β)]; ring
    · rw [← sq_abs (Real.sin β)]; nlinarith [abs_nonneg (Real.sin β)]
  have hpos : 0 < ‖mobDen β κ z‖ * ‖mobDen β κ z'‖ := mul_pos (by linarith) (by linarith)
  rw [hc2, div_le_iff₀ hpos]
  have hcs : Real.cos β + |Real.sin β| ≤ 2 := by
    linarith [Real.cos_le_one β, (abs_le.2 ⟨Real.neg_one_le_sin β, Real.sin_le_one β⟩ :
      |Real.sin β| ≤ 1)]
  have hP : m * m ≤ ‖mobDen β κ z‖ * ‖mobDen β κ z'‖ :=
    mul_le_mul h1 h2 hm0.le (norm_nonneg _)
  have hzz := norm_nonneg (z - z')
  calc m * (Real.cos β + |Real.sin β|) * ‖z - z'‖ ≤ m * 2 * ‖z - z'‖ := by gcongr
    _ = 2 / m * ‖z - z'‖ * (m * m) := by field_simp
    _ ≤ 2 / m * ‖z - z'‖ * (‖mobDen β κ z‖ * ‖mobDen β κ z'‖) := by gcongr

theorem injOn_mob {β κ : ℝ} (hβ : |Real.sin β| < Real.cos β) :
    InjOn (mob β κ) {z | mobDen β κ z ≠ 0} := by
  intro z hz z' hz' h
  have := mob_sub hz hz'
  rw [h, sub_self, eq_comm, div_eq_zero_iff] at this
  rcases this with h0 | h0
  · rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exfalso
        rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
          Complex.ofReal_eq_zero, ← sq_abs (Real.sin β)] at h2
        nlinarith [abs_nonneg (Real.sin β)]
      · exact absurd h2 (Complex.exp_ne_zero _)
    · exact sub_eq_zero.1 h1
  · exact absurd h0 (mul_ne_zero hz hz')

theorem differentiableAt_mob {β κ : ℝ} {z : ℂ} (hz : mobDen β κ z ≠ 0) :
    DifferentiableAt ℂ (mob β κ) z := by
  unfold mob
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) hz

lemma cos_sin_exp (β : ℝ) :
    (Real.cos β : ℂ) = (Complex.exp (β * Complex.I) + (Complex.exp (β * Complex.I))⁻¹) / 2 ∧
    (Real.sin β : ℂ) * Complex.I =
      (Complex.exp (β * Complex.I) - (Complex.exp (β * Complex.I))⁻¹) / 2 := by
  rw [Complex.ofReal_cos, Complex.ofReal_sin, Complex.cos, Complex.sin, ← Complex.exp_neg,
    neg_mul]
  refine ⟨rfl, ?_⟩
  linear_combination (Complex.exp (-(↑β * Complex.I)) - Complex.exp (↑β * Complex.I)) / 2 *
    Complex.I_sq

/-- `mob` sends `e^{i(2β − κ)}` to `1`. -/
theorem mob_val_one {β κ : ℝ} (hβ : |Real.sin β| < Real.cos β) :
    mob β κ (Complex.exp ((2 * β - κ : ℝ) * Complex.I)) = 1 := by
  have hz : ‖Complex.exp ((2 * β - κ : ℝ) * Complex.I)‖ ≤ 1 := (norm_exp_mul_I _).le
  have hd := mobDen_ne (κ := κ) hβ hz
  rw [mob_eq, div_eq_one_iff_eq hd]
  have he : Complex.exp (κ * Complex.I) * Complex.exp ((2 * β - κ : ℝ) * Complex.I) =
      Complex.exp (β * Complex.I) ^ 2 := by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  obtain ⟨hc, hs⟩ := cos_sin_exp β
  have hq := Complex.exp_ne_zero (β * Complex.I)
  unfold mobDen
  rw [mul_assoc (Real.cos β : ℂ), he, mul_assoc ((Real.sin β : ℂ) * Complex.I), he, hc, hs]
  field_simp
  ring

/-- `mob` sends `e^{i(π − 2β − κ)}` to `−1`. -/
theorem mob_val_neg_one {β κ : ℝ} (hβ : |Real.sin β| < Real.cos β) :
    mob β κ (Complex.exp ((π - 2 * β - κ : ℝ) * Complex.I)) = -1 := by
  have hz : ‖Complex.exp ((π - 2 * β - κ : ℝ) * Complex.I)‖ ≤ 1 := (norm_exp_mul_I _).le
  have hd := mobDen_ne (κ := κ) hβ hz
  rw [mob_eq, div_eq_iff hd]
  have he : Complex.exp (κ * Complex.I) * Complex.exp ((π - 2 * β - κ : ℝ) * Complex.I) =
      -(Complex.exp (β * Complex.I) ^ 2)⁻¹ := by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_neg]
    have : (κ : ℂ) * Complex.I + ((π - 2 * β - κ : ℝ) : ℂ) * Complex.I =
        -(((2 : ℕ) : ℂ) * (β * Complex.I)) + π * Complex.I := by push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  obtain ⟨hc, hs⟩ := cos_sin_exp β
  have hq := Complex.exp_ne_zero (β * Complex.I)
  unfold mobDen
  rw [mul_assoc (Real.cos β : ℂ), he, mul_assoc ((Real.sin β : ℂ) * Complex.I), he, hc, hs]
  field_simp
  ring

end LQGMetric.DDDF.L12

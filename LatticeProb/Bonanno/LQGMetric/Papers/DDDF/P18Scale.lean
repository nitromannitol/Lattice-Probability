/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Scale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P16Indep
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw

/-!
# DDDF (2.30): scaling of crossing lengths (input of DDDF Proposition 18, Step 2)

DDDF (arXiv:1904.08021, `tightness.tex` l. 490): `L^{(m,n)}_{a,b}(φ) =ᵈ 2^{-m} L^{(n−m)}_{2^m a, 2^m b}(φ)`
(used in Prop 18, Step 2, l. 914: `L^{(m,n)}_{3,1}(φ) =ᵈ 2^{-m} L^{(n−m)}_{3·2^m, 2^m}(φ)`).
Proof (DDDF: "by scaling"): the deterministic change of variables `z ↦ r z` in the path
integral (`crossLenIn_image_mul`, from `crossLenIn_image_le` applied to `z ↦ rz` and
`z ↦ r⁻¹z`), and the scaling of the field `φ_{a,b}(r ·) =ᵈ φ_{a/r, b/r}` (`map_phi_scale`,
DDDF.D2.phi (ii)) for `r = 2^{-m}`, transported to crossing lengths by
`measure_crossLenIn_eq`. Own routine write-up of DDDF's one line.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}

/-- crossing lengths of a dilated domain: `L(rK; g) = r L(K; g(r ·))` -/
theorem crossLenIn_image_mul (ξ : ℝ) (g : ℂ → ℝ) (K A B : Set ℂ) {r : ℝ} (hr : 0 < r) :
    crossLenIn ξ g ((fun z => (r : ℂ) * z) '' K) ((fun z => (r : ℂ) * z) '' A)
        ((fun z => (r : ℂ) * z) '' B) =
      ENNReal.ofReal r * crossLenIn ξ (fun x => g ((r : ℂ) * x)) K A B := by
  have hD : ∀ c : ℂ, DifferentiableOn ℂ (fun z => c * z) univ := fun c => by fun_prop
  have hd : ∀ c : ℂ, ∀ x : ℂ, deriv (fun z => c * z) x = c := fun c x => by
    simp
  refine le_antisymm ?_ ?_
  · exact crossLenIn_image_le (ξ := ξ) (g := g) isOpen_univ (subset_univ K) (hD r) hr
      (fun x _ => by rw [hd]; simp [abs_of_pos hr])
  · have h := crossLenIn_image_le (ξ := ξ) (g := fun x => g ((r : ℂ) * x))
      (K := (fun z => (r : ℂ) * z) '' K) (A := (fun z => (r : ℂ) * z) '' A)
      (B := (fun z => (r : ℂ) * z) '' B) isOpen_univ (subset_univ _) (hD ((r : ℂ)⁻¹))
      (inv_pos.2 hr) (fun x _ => by rw [hd]; simp [abs_of_pos hr])
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    have e : ∀ S : Set ℂ, (fun z => (r : ℂ)⁻¹ * z) '' ((fun z => (r : ℂ) * z) '' S) = S :=
      fun S => by rw [image_image]; simp [inv_mul_cancel_left₀ hr0]
    have e2 : ((fun x => g ((r : ℂ) * x)) ∘ fun z => (r : ℂ)⁻¹ * z) = g :=
      funext fun x => by simp [mul_inv_cancel_left₀ hr0]
    rw [e, e, e, e2] at h
    calc ENNReal.ofReal r * crossLenIn ξ (fun x => g ((r : ℂ) * x)) K A B
        ≤ ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * crossLenIn ξ g ((fun z => (r : ℂ) * z) '' K)
            ((fun z => (r : ℂ) * z) '' A) ((fun z => (r : ℂ) * z) '' B)) := by gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne',
            ENNReal.ofReal_one, one_mul]

lemma image_mul_rectAB_toSet {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    (fun z => (r : ℂ) * z) '' (rectAB a b).toSet = (rectAB (r * a) (r * b)).toSet := by
  ext z
  simp only [mem_image, mem_rectAB_toSet, mem_Icc]
  constructor
  · rintro ⟨w, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    refine ⟨⟨by positivity, by nlinarith⟩, by positivity, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨(r : ℂ)⁻¹ * z, ?_, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hr.ne') z⟩
    have e1 : ((r : ℂ)⁻¹ * z).re = z.re / r := by
      rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, div_eq_inv_mul]
    have e2 : ((r : ℂ)⁻¹ * z).im = z.im / r := by
      rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, div_eq_inv_mul]
    rw [e1, e2]
    refine ⟨⟨by positivity, ?_⟩, by positivity, ?_⟩ <;> rw [div_le_iff₀ hr] <;> linarith

lemma image_mul_rectAB_side₁ {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    (fun z => (r : ℂ) * z) '' (rectAB a b).side₁ = (rectAB (r * a) (r * b)).side₁ := by
  ext z
  simp only [mem_image, mem_rectAB_side₁, mem_Icc]
  constructor
  · rintro ⟨w, ⟨h1, h3, h4⟩, rfl⟩
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero, h1, mul_zero]
    exact ⟨trivial, by positivity, by nlinarith⟩
  · rintro ⟨h1, h3, h4⟩
    refine ⟨(r : ℂ)⁻¹ * z, ?_, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hr.ne') z⟩
    have e1 : ((r : ℂ)⁻¹ * z).re = z.re / r := by
      rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, div_eq_inv_mul]
    have e2 : ((r : ℂ)⁻¹ * z).im = z.im / r := by
      rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, div_eq_inv_mul]
    rw [e1, e2, h1, zero_div]
    refine ⟨rfl, by positivity, ?_⟩
    rw [div_le_iff₀ hr]; linarith

lemma image_mul_rectAB_side₂ {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    (fun z => (r : ℂ) * z) '' (rectAB a b).side₂ = (rectAB (r * a) (r * b)).side₂ := by
  ext z
  simp only [mem_image, mem_rectAB_side₂, mem_Icc]
  constructor
  · rintro ⟨w, ⟨h1, h3, h4⟩, rfl⟩
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero, h1]
    exact ⟨trivial, by positivity, by nlinarith⟩
  · rintro ⟨h1, h3, h4⟩
    refine ⟨(r : ℂ)⁻¹ * z, ?_, mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 hr.ne') z⟩
    have e1 : ((r : ℂ)⁻¹ * z).re = z.re / r := by
      rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, div_eq_inv_mul]
    have e2 : ((r : ℂ)⁻¹ * z).im = z.im / r := by
      rw [← Complex.ofReal_inv, Complex.im_ofReal_mul, div_eq_inv_mul]
    rw [e1, e2, h1]
    refine ⟨by field_simp, by positivity, ?_⟩
    rw [div_le_iff₀ hr]; linarith

/-- `L(R_{ra, rb}; f) = r L(R_{a,b}; f(r ·))` -/
theorem rectLen_rectAB_mul (f : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    rectLen ξ f (rectAB (r * a) (r * b)) =
      ENNReal.ofReal r * rectLen ξ (fun x => f ((r : ℂ) * x)) (rectAB a b) := by
  unfold rectLen
  rw [← image_mul_rectAB_toSet hr, ← image_mul_rectAB_side₁ hr, ← image_mul_rectAB_side₂ hr]
  exact crossLenIn_image_mul ξ f _ _ _ hr

/-- **DDDF (2.30)**: `L^{(m,n)}_{a,b}(φ) =ᵈ 2^{-m} L^{(n−m)}_{2^m a, 2^m b}(φ)`. -/
theorem dddf_eq230 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (a b : ℝ) {m n : ℕ}
    (hmn : m ≤ n) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | lenMN ξ W P a b m n ω ∈ S} =
      P {ω | (2 : ℝ)⁻¹ ^ m * lenMN ξ W P ((2 : ℝ) ^ m * a) ((2 : ℝ) ^ m * b) 0 (n - m) ω ∈ S} := by
  have := hW.isProbabilityMeasure
  set r : ℝ := (2 : ℝ)⁻¹ ^ m
  have hr : 0 < r := by positivity
  have hφ := isPhiVersion_phiMN hW hmn
  have hφ0 := isPhiVersion_phiMN hW (Nat.zero_le (n - m))
  set Y₁ : ℂ → Ω → ℝ := fun x ω => phiMN W P m n ((r : ℂ) * x) ω
  -- the law of `x ↦ φ_{m,n}(r x)` is that of `φ_{0,n-m}`
  have hra : (2 : ℝ)⁻¹ ^ n / r = (2 : ℝ)⁻¹ ^ (n - m) := by
    simp only [r]; rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel hmn]
  have hrb : (2 : ℝ)⁻¹ ^ m / r = (2 : ℝ)⁻¹ ^ 0 := by simp only [r]; field_simp
  have hlaw := map_modification_scale hW (a := (2 : ℝ)⁻¹ ^ n) (b := (2 : ℝ)⁻¹ ^ m) (by positivity)
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn) hr (Y₁ := Y₁)
    (Y₂ := phiMN W P 0 (n - m)) (fun x => hφ.meas _) hφ0.meas (fun x => hφ.ae_eq _)
    (fun x => by rw [hra, hrb]; exact hφ0.ae_eq x) (F := id) measurable_id
  simp only [id] at hlaw
  set R := rectAB ((2 : ℝ) ^ m * a) ((2 : ℝ) ^ m * b)
  have hrR : rectAB a b = rectAB (r * ((2 : ℝ) ^ m * a)) (r * ((2 : ℝ) ^ m * b)) := by
    simp only [r]; rw [← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ two_ne_zero,
      one_pow, one_mul, one_mul]
  set T : Set ℝ≥0∞ := {v | r * v.toReal ∈ S}
  have hT : MeasurableSet T := (measurable_const.mul ENNReal.measurable_toReal) hS
  have h1 : {ω | lenMN ξ W P a b m n ω ∈ S} =
      {ω | crossLenIn ξ (fun x => Y₁ x ω) R.toSet R.side₁ R.side₂ ∈ T} := by
    ext ω
    show (rectLen ξ (fun x => phiMN W P m n x ω) (rectAB a b)).toReal ∈ S ↔ _
    rw [hrR, rectLen_rectAB_mul _ hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le]
    rfl
  have h2 : {ω | r * lenMN ξ W P ((2 : ℝ) ^ m * a) ((2 : ℝ) ^ m * b) 0 (n - m) ω ∈ S} =
      {ω | crossLenIn ξ (fun x => phiMN W P 0 (n - m) x ω) R.toSet R.side₁ R.side₂ ∈ T} := rfl
  rw [h1, h2]
  exact measure_crossLenIn_eq (MarkedRect.isCompact_toSet R)
    (fun ω => (hφ.cont ω).comp (continuous_const.mul continuous_id)) (fun x => hφ.meas _)
    hφ0.cont hφ0.meas hlaw hT

end DDDF
end LQGMetric

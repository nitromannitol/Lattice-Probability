import Mathlib

/-!
# Raic's Lemma 2.7: the real-analysis core (L12a) and the Gaussian tensor bounds (L9)

Packet P5 of the staged formalisation of Raic, "A multivariate Berry-Esseen theorem with explicit
constants" (arXiv:1802.06475, Thm 1.3).

* Part 1 is pure real analysis.  `mvbe_integral_mul_tan_le` integrates the two pointwise bounds
  (2.17) and (2.20) of the paper against `tan`, which gives (2.21).  `mvbe_keyEstimate_optimised`
  optimises the splitting angle `β` and gives the right-hand side of (2.11),
  `c3/(6σ³) + √(2(1+κ)c1c3) (γ*/σ + 4D/ε)`.  The `_of_measurable` variants replace the
  integrability hypothesis on `h * tan` by measurability and nonnegativity of `h`.
* Part 2 is Lemma 2.5: `mvbe_gaussian_hermite_integral_le` bounds the Gaussian integral of
  `f(z) He_r(⟪z,u⟫/‖u‖)` (`r ∈ {1,2,3}`) by `c_r M`, after the reduction of the law of `z ↦ ⟪z,û⟫`
  to `gaussianReal 0 1`; `mvbe_iteratedFDeriv_gaussDensity` is the tensor identity
  `∇^r φ_d(z)[u^r] = (-1)^r He_r(⟪z,u⟫/‖u‖) ‖u‖^r φ_d(z)`; `mvbe_stdGaussian_eq_withDensity`
  is the density of `stdGaussian`; `mvbe_lemma_2_5` is the lemma in the paper's form.
* Lemma 2.6 (differentiation of the Mehler smoothing `U_α f`) is not in this file: it needs the
  smoothness of `U_α f`, which is the Mathlib gap of packet L7.
-/

open MeasureTheory Set Real ProbabilityTheory Polynomial
open scoped RealInnerProductSpace ENNReal NNReal

namespace LatticeProb

/-! ### Exact integrals -/

/-- `∫_β^{π/2} cos² a sin a da = cos³ β / 3`. -/
theorem mvbe_integral_cos_sq_mul_sin (β : ℝ) :
    ∫ a in β..(π / 2), cos a ^ 2 * sin a = cos β ^ 3 / 3 := by
  have hderiv : ∀ x ∈ uIcc β (π / 2),
      HasDerivAt (fun a => -(cos a ^ 3 / 3)) (cos x ^ 2 * sin x) x := by
    intro x _
    have h : HasDerivAt (fun a => -(cos a ^ 3 / 3))
        (-(((3 : ℕ) : ℝ) * cos x ^ (3 - 1) * -sin x / 3)) x :=
      (((hasDerivAt_cos x).pow 3).div_const 3).neg
    refine h.congr_deriv ?_
    simp
    ring
  have hint : IntervalIntegrable (fun a => cos a ^ 2 * sin a) volume β (π / 2) :=
    (by fun_prop : Continuous fun a : ℝ => cos a ^ 2 * sin a).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [cos_pi_div_two]

/-- `∫_β^{π/2} cot² a da = cot β - (π/2 - β)` for `0 < β < π/2`. -/
theorem mvbe_integral_cot_sq {β : ℝ} (hβ0 : 0 < β) (hβ : β < π / 2) :
    ∫ a in β..(π / 2), (cos a / sin a) ^ 2 = cos β / sin β - (π / 2 - β) := by
  have hsin : ∀ x ∈ uIcc β (π / 2), 0 < sin x := by
    intro x hx
    rw [uIcc_of_le hβ.le] at hx
    exact sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hβ0 hx.1) (by linarith [hx.2, pi_pos])
  have hderiv : ∀ x ∈ uIcc β (π / 2),
      HasDerivAt (fun a => -(cos a / sin a) - a) ((cos x / sin x) ^ 2) x := by
    intro x hx
    have hs := (hsin x hx).ne'
    have h : HasDerivAt (fun a => -(cos a / sin a) - a)
        (-((-sin x * sin x - cos x * cos x) / sin x ^ 2) - 1) x :=
      (((hasDerivAt_cos x).div (hasDerivAt_sin x) hs).neg).sub (hasDerivAt_id x)
    refine h.congr_deriv ?_
    have hs2 : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
    field_simp
    nlinarith [hs2]
  have hcont : ContinuousOn (fun a => (cos a / sin a) ^ 2) (uIcc β (π / 2)) := by
    refine ContinuousOn.pow (ContinuousOn.div continuous_cos.continuousOn
      continuous_sin.continuousOn (fun x hx => (hsin x hx).ne')) 2
  have hint : IntervalIntegrable (fun a => (cos a / sin a) ^ 2) volume β (π / 2) :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [cos_pi_div_two]
  ring

/-! ### Integration of the two pointwise bounds (Raic (2.21)) -/

/-- Raic's (2.21), sharp form: the exact values of the three elementary integrals are kept.
The hypotheses `0 ≤ h`, `0 ≤ c`, `0 ≤ c3`, `0 ≤ X` are not needed here (only `tan ≥ 0` on
`(0, π/2)` is used). -/
theorem mvbe_integral_mul_tan_le_exact
    (c c3 ε X σ D β : ℝ) (hε : 0 < ε) (hσ : 0 < σ) (hD : 0 ≤ D) (hβ0 : 0 < β)
    (hβ : β < π / 2) (h : ℝ → ℝ)
    (h1 : ∀ a ∈ Ioc 0 β, h a ≤ c * cos a ^ 2 / (ε * sin a) * X)
    (h2 : ∀ a ∈ Ico β (π / 2),
      h a ≤ c3 * cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (cos a / sin a) ^ 3)
    (hint : IntervalIntegrable (fun a => h a * tan a) volume 0 (π / 2)) :
    (∫ a in (0 : ℝ)..(π / 2), h a * tan a) ≤
      (c / ε) * sin β * X + c3 * cos β ^ 3 / (6 * σ ^ 3)
        + c3 * D * (cos β / sin β - (π / 2 - β)) := by
  have hβle : β ≤ π / 2 := hβ.le
  have hint1 : IntervalIntegrable (fun a => h a * tan a) volume 0 β :=
    hint.mono_set (by
      rw [uIcc_of_le hβ0.le, uIcc_of_le (by linarith [pi_pos])]
      exact Icc_subset_Icc le_rfl hβle)
  have hint2 : IntervalIntegrable (fun a => h a * tan a) volume β (π / 2) :=
    hint.mono_set (by
      rw [uIcc_of_le hβle, uIcc_of_le (by linarith [pi_pos])]
      exact Icc_subset_Icc hβ0.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  -- first piece
  have hP1 : (∫ a in (0 : ℝ)..β, h a * tan a) ≤ (c / ε) * sin β * X := by
    have hg : IntervalIntegrable (fun a => (c / ε * X) * cos a) volume 0 β :=
      (by fun_prop : Continuous fun a : ℝ => (c / ε * X) * cos a).intervalIntegrable _ _
    have hle := intervalIntegral.integral_mono_on_of_le_Ioo hβ0.le hint1 hg (by
      intro x hx
      have hx0 : 0 < x := hx.1
      have hxb : x < π / 2 := lt_trans hx.2 hβ
      have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
      have hcos : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxb⟩
      have htan : 0 ≤ tan x := (tan_pos_of_pos_of_lt_pi_div_two hx0 hxb).le
      calc h x * tan x ≤ (c * cos x ^ 2 / (ε * sin x) * X) * tan x :=
            mul_le_mul_of_nonneg_right (h1 x ⟨hx0, hx.2.le⟩) htan
        _ = (c / ε * X) * cos x := by
            rw [tan_eq_sin_div_cos]
            field_simp)
    have hint_eq : ∫ a in (0 : ℝ)..β, (c / ε * X) * cos a = (c / ε) * sin β * X := by
      rw [intervalIntegral.integral_const_mul, integral_cos]
      simp
      ring
    linarith
  -- second piece
  have hsin : ∀ x ∈ uIcc β (π / 2), 0 < sin x := by
    intro x hx
    rw [uIcc_of_le hβle] at hx
    exact sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hβ0 hx.1) (by linarith [hx.2, pi_pos])
  have hI1 : IntervalIntegrable (fun a => cos a ^ 2 * sin a) volume β (π / 2) :=
    (by fun_prop : Continuous fun a : ℝ => cos a ^ 2 * sin a).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun a => (cos a / sin a) ^ 2) volume β (π / 2) :=
    (ContinuousOn.pow (ContinuousOn.div continuous_cos.continuousOn
      continuous_sin.continuousOn (fun x hx => (hsin x hx).ne')) 2).intervalIntegrable
  have hg2 : IntervalIntegrable
      (fun a => c3 / (2 * σ ^ 3) * (cos a ^ 2 * sin a) + c3 * D * (cos a / sin a) ^ 2)
      volume β (π / 2) :=
    (hI1.const_mul _).add (hI2.const_mul _)
  have hP2 : (∫ a in β..(π / 2), h a * tan a) ≤
      c3 * cos β ^ 3 / (6 * σ ^ 3) + c3 * D * (cos β / sin β - (π / 2 - β)) := by
    have hle := intervalIntegral.integral_mono_on_of_le_Ioo hβle hint2 hg2 (by
      intro x hx
      have hx0 : 0 < x := lt_trans hβ0 hx.1
      have hxb : x < π / 2 := hx.2
      have hsx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
      have hcx : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxb⟩
      have htan : 0 ≤ tan x := (tan_pos_of_pos_of_lt_pi_div_two hx0 hxb).le
      calc h x * tan x
          ≤ (c3 * cos x ^ 3 / (2 * σ ^ 3) + c3 * D * (cos x / sin x) ^ 3) * tan x :=
            mul_le_mul_of_nonneg_right (h2 x ⟨hx.1.le, hx.2⟩) htan
        _ = c3 / (2 * σ ^ 3) * (cos x ^ 2 * sin x) + c3 * D * (cos x / sin x) ^ 2 := by
            rw [tan_eq_sin_div_cos]
            field_simp)
    have hval : ∫ a in β..(π / 2),
        (c3 / (2 * σ ^ 3) * (cos a ^ 2 * sin a) + c3 * D * (cos a / sin a) ^ 2)
        = c3 * cos β ^ 3 / (6 * σ ^ 3) + c3 * D * (cos β / sin β - (π / 2 - β)) := by
      rw [intervalIntegral.integral_add (hI1.const_mul _) (hI2.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        mvbe_integral_cos_sq_mul_sin, mvbe_integral_cot_sq hβ0 hβ]
      field_simp
      ring
    linarith
  linarith

/-- Raic's (2.21), in the form asked for in the brief: `sin β ≤ tan β`, `cos³ β ≤ 1` and
`cot β - (π/2 - β) ≤ cot β`. -/
theorem mvbe_integral_mul_tan_le
    (c c3 ε X σ D β : ℝ) (hc : 0 ≤ c) (hc3 : 0 ≤ c3) (hε : 0 < ε) (hX : 0 ≤ X)
    (hσ : 0 < σ) (hD : 0 ≤ D) (hβ0 : 0 < β) (hβ : β < π / 2) (h : ℝ → ℝ)
    (h1 : ∀ a ∈ Ioc 0 β, h a ≤ c * cos a ^ 2 / (ε * sin a) * X)
    (h2 : ∀ a ∈ Ico β (π / 2),
      h a ≤ c3 * cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (cos a / sin a) ^ 3)
    (hint : IntervalIntegrable (fun a => h a * tan a) volume 0 (π / 2)) :
    (∫ a in (0 : ℝ)..(π / 2), h a * tan a) ≤
      (c / ε) * tan β * X + c3 / (6 * σ ^ 3) + c3 * D * (cos β / sin β) := by
  have hex := mvbe_integral_mul_tan_le_exact c c3 ε X σ D β hε hσ hD hβ0 hβ h h1 h2 hint
  have hsin : 0 < sin β := sin_pos_of_pos_of_lt_pi hβ0 (by linarith [pi_pos])
  have hcos : 0 < cos β := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hβ⟩
  have hcos1 : cos β ≤ 1 := cos_le_one β
  have hsin_tan : sin β ≤ tan β := by
    rw [tan_eq_sin_div_cos, le_div_iff₀ hcos]
    nlinarith
  have hcT : 0 ≤ c / ε * X := by positivity
  have h1' : (c / ε) * sin β * X ≤ (c / ε) * tan β * X := by
    have := mul_le_mul_of_nonneg_left hsin_tan hcT
    linarith
  have hcos3 : cos β ^ 3 ≤ 1 := pow_le_one₀ hcos.le hcos1
  have h2' : c3 * cos β ^ 3 / (6 * σ ^ 3) ≤ c3 / (6 * σ ^ 3) := by
    have h6 : 0 < 6 * σ ^ 3 := by positivity
    rw [div_le_div_iff_of_pos_right h6]
    nlinarith
  have hcD : 0 ≤ c3 * D := mul_nonneg hc3 hD
  have h3' : c3 * D * (cos β / sin β - (π / 2 - β)) ≤ c3 * D * (cos β / sin β) := by
    have := mul_le_mul_of_nonneg_left (by linarith : cos β / sin β - (π / 2 - β) ≤ cos β / sin β)
      hcD
    linarith
  linarith

/-- The integrability hypothesis of the integrated bound follows from measurability, `0 ≤ h`
on `(0, π/2)` and the two pointwise bounds. -/
theorem mvbe_intervalIntegrable_mul_tan
    (c c3 ε X σ D β : ℝ) (hc3 : 0 ≤ c3) (hε : 0 < ε)
    (hσ : 0 < σ) (hD : 0 ≤ D) (hβ0 : 0 < β) (hβ : β < π / 2) (h : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Ioc 0 (π / 2))))
    (hnn : ∀ a ∈ Ioo 0 (π / 2), 0 ≤ h a)
    (h1 : ∀ a ∈ Ioc 0 β, h a ≤ c * cos a ^ 2 / (ε * sin a) * X)
    (h2 : ∀ a ∈ Ico β (π / 2),
      h a ≤ c3 * cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (cos a / sin a) ^ 3) :
    IntervalIntegrable (fun a => h a * tan a) volume 0 (π / 2) := by
  have hβle : β ≤ π / 2 := hβ.le
  have hpi : 0 < π / 2 := by linarith [pi_pos]
  have htanm : Measurable tan := by
    have : (tan : ℝ → ℝ) = fun x => sin x / cos x := by funext x; exact tan_eq_sin_div_cos x
    rw [this]; exact measurable_sin.div measurable_cos
  have hm : AEStronglyMeasurable (fun a => h a * tan a) (volume.restrict (Ioc 0 (π / 2))) :=
    hmeas.mul htanm.aestronglyMeasurable
  -- first piece
  have hI1 : IntervalIntegrable (fun a => h a * tan a) volume 0 β := by
    have hg : IntervalIntegrable (fun a => (c / ε * X) * cos a) volume 0 β :=
      (by fun_prop : Continuous fun a : ℝ => (c / ε * X) * cos a).intervalIntegrable _ _
    refine hg.mono_fun' ?_ ?_
    · refine hm.mono_measure (Measure.restrict_mono ?_ le_rfl)
      rw [uIoc_of_le hβ0.le]
      exact Ioc_subset_Ioc le_rfl hβle
    · rw [uIoc_of_le hβ0.le]
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
      intro x hx
      have hx0 : 0 < x := hx.1
      have hxb : x < π / 2 := lt_of_le_of_lt hx.2 hβ
      have hsin : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
      have hcos : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxb⟩
      have htan : 0 ≤ tan x := (tan_pos_of_pos_of_lt_pi_div_two hx0 hxb).le
      have hhx := hnn x ⟨hx0, hxb⟩
      beta_reduce
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hhx htan)]
      calc h x * tan x ≤ (c * cos x ^ 2 / (ε * sin x) * X) * tan x :=
            mul_le_mul_of_nonneg_right (h1 x hx) htan
        _ = (c / ε * X) * cos x := by
            rw [tan_eq_sin_div_cos]
            field_simp
  -- second piece
  have hsin : ∀ x ∈ uIcc β (π / 2), 0 < sin x := by
    intro x hx
    rw [uIcc_of_le hβle] at hx
    exact sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hβ0 hx.1) (by linarith [hx.2, pi_pos])
  have hI2 : IntervalIntegrable (fun a => h a * tan a) volume β (π / 2) := by
    have hJ1 : IntervalIntegrable (fun a => cos a ^ 2 * sin a) volume β (π / 2) :=
      (by fun_prop : Continuous fun a : ℝ => cos a ^ 2 * sin a).intervalIntegrable _ _
    have hJ2 : IntervalIntegrable (fun a => (cos a / sin a) ^ 2) volume β (π / 2) :=
      (ContinuousOn.pow (ContinuousOn.div continuous_cos.continuousOn
        continuous_sin.continuousOn (fun x hx => (hsin x hx).ne')) 2).intervalIntegrable
    have hg : IntervalIntegrable
        (fun a => c3 / (2 * σ ^ 3) * (cos a ^ 2 * sin a) + c3 * D * (cos a / sin a) ^ 2)
        volume β (π / 2) := (hJ1.const_mul _).add (hJ2.const_mul _)
    refine hg.mono_fun' ?_ ?_
    · refine hm.mono_measure (Measure.restrict_mono ?_ le_rfl)
      rw [uIoc_of_le hβle]
      exact Ioc_subset_Ioc hβ0.le le_rfl
    · rw [uIoc_of_le hβle]
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
      intro x hx
      have hx0 : 0 < x := lt_trans hβ0 hx.1
      have hsx : 0 < sin x := sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos, hx.2])
      have hg0 : 0 ≤ c3 / (2 * σ ^ 3) * (cos x ^ 2 * sin x) + c3 * D * (cos x / sin x) ^ 2 := by
        positivity
      rcases eq_or_lt_of_le hx.2 with hxe | hxlt
      · beta_reduce
        rw [hxe, tan_pi_div_two, mul_zero, norm_zero]
        rw [hxe] at hg0
        exact hg0
      · have hcx : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hxlt⟩
        have htan : 0 ≤ tan x := (tan_pos_of_pos_of_lt_pi_div_two hx0 hxlt).le
        have hhx := hnn x ⟨hx0, hxlt⟩
        beta_reduce
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hhx htan)]
        calc h x * tan x
            ≤ (c3 * cos x ^ 3 / (2 * σ ^ 3) + c3 * D * (cos x / sin x) ^ 3) * tan x :=
              mul_le_mul_of_nonneg_right (h2 x ⟨hx.1.le, hxlt⟩) htan
          _ = c3 / (2 * σ ^ 3) * (cos x ^ 2 * sin x) + c3 * D * (cos x / sin x) ^ 2 := by
              rw [tan_eq_sin_div_cos]
              field_simp
  exact hI1.trans hI2

/-- Raic's (2.21) with measurability and nonnegativity of `h` in place of the integrability
hypothesis. -/
theorem mvbe_integral_mul_tan_le_of_measurable
    (c c3 ε X σ D β : ℝ) (hc : 0 ≤ c) (hc3 : 0 ≤ c3) (hε : 0 < ε) (hX : 0 ≤ X)
    (hσ : 0 < σ) (hD : 0 ≤ D) (hβ0 : 0 < β) (hβ : β < π / 2) (h : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Ioc 0 (π / 2))))
    (hnn : ∀ a ∈ Ioo 0 (π / 2), 0 ≤ h a)
    (h1 : ∀ a ∈ Ioc 0 β, h a ≤ c * cos a ^ 2 / (ε * sin a) * X)
    (h2 : ∀ a ∈ Ico β (π / 2),
      h a ≤ c3 * cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (cos a / sin a) ^ 3) :
    (∫ a in (0 : ℝ)..(π / 2), h a * tan a) ≤
      (c / ε) * tan β * X + c3 / (6 * σ ^ 3) + c3 * D * (cos β / sin β) :=
  mvbe_integral_mul_tan_le c c3 ε X σ D β hc hc3 hε hX hσ hD hβ0 hβ h h1 h2
    (mvbe_intervalIntegrable_mul_tan c c3 ε X σ D β hc3 hε hσ hD hβ0 hβ h hmeas hnn h1 h2)

/-! ### Optimisation in the splitting angle (Raic (2.11)) -/

/-- On `(0, π/2)`: `cot β = 1 / tan β`. -/
theorem mvbe_cot_eq_inv_tan {β : ℝ} (hβ0 : 0 < β) (hβ : β < π / 2) :
    cos β / sin β = 1 / tan β := by
  have hsin : 0 < sin β := sin_pos_of_pos_of_lt_pi hβ0 (by linarith [pi_pos])
  have hcos : 0 < cos β := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hβ⟩
  rw [tan_eq_sin_div_cos]
  field_simp

/-- AM-GM for `A tan β + B cot β`: it is at least `2 √(A B)`. -/
theorem mvbe_two_sqrt_le_tan_add_cot {A B β : ℝ} (hA : 0 < A) (hB : 0 < B) (hβ0 : 0 < β)
    (hβ : β < π / 2) :
    2 * sqrt (A * B) ≤ A * tan β + B * (cos β / sin β) := by
  have htpos : 0 < tan β := tan_pos_of_pos_of_lt_pi_div_two hβ0 hβ
  have hsq : sqrt (A * B) ^ 2 = A * B := sq_sqrt (mul_pos hA hB).le
  rw [mvbe_cot_eq_inv_tan hβ0 hβ]
  set t := tan β
  have h1 : 2 * sqrt (A * B) * t ≤ A * t ^ 2 + B := by
    nlinarith [sq_nonneg (A * t - sqrt (A * B)), hsq, hA]
  have : A * t + B * (1 / t) = (A * t ^ 2 + B) / t := by field_simp
  rw [this, le_div_iff₀ htpos]
  exact h1

/-- Equality in the AM-GM step at the optimiser `β = arctan (√(B/A))`. -/
theorem mvbe_tan_add_cot_at_opt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * tan (arctan (sqrt (B / A)))
      + B * (cos (arctan (sqrt (B / A))) / sin (arctan (sqrt (B / A)))) = 2 * sqrt (A * B) := by
  have hq : 0 < sqrt (B / A) := sqrt_pos.2 (div_pos hB hA)
  have hsq : sqrt (B / A) ^ 2 = B / A := sq_sqrt (div_pos hB hA).le
  have hAB : sqrt (A * B) = A * sqrt (B / A) := by
    rw [sqrt_eq_iff_mul_self_eq (mul_pos hA hB).le (by positivity)]
    have h2 : B = A * sqrt (B / A) ^ 2 := by rw [hsq]; field_simp
    nlinarith [h2]
  rw [mvbe_cot_eq_inv_tan (arctan_pos.2 hq) (arctan_lt_pi_div_two _), tan_arctan, hAB]
  have h2 : B = A * sqrt (B / A) ^ 2 := by rw [hsq]; field_simp
  set q := sqrt (B / A)
  rw [h2]
  field_simp
  ring

/-- Raic's Lemma 2.7, the optimised form (2.11): once the two pointwise bounds (2.17) and (2.20)
hold for every `α ∈ (0, π/2)` (as they do in the paper, where they do not depend on `β`), the
integral is at most `c3/(6σ³) + √(2(1+κ)c1c3) (γ*/σ + 4D/ε)`.  Here `c1 > 0`, `c3 > 0`, `κ ≥ 0`
(in the paper `c1 = √(2/π)`, `c3 = ∫|He₃|φ`, `κ = 1`) and `γ` stands for `γ*(A|ρ)`. The proof
chooses `β = arctan (ε s / (4(1+κ)c1))` with `s = √(2(1+κ)c1c3)`, which is the paper's
`arctan (ε √(c3/(8(1+κ)c1)))`. -/
theorem mvbe_keyEstimate_optimised
    (c1 c3 κ γ σ ε D : ℝ) (hc1 : 0 < c1) (hc3 : 0 < c3) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ)
    (hε : 0 < ε) (hσ : 0 < σ) (hD : 0 ≤ D) (h : ℝ → ℝ)
    (h1 : ∀ a ∈ Ioo 0 (π / 2),
      h a ≤ 4 * (1 + κ) * c1 * cos a ^ 2 / (ε * sin a) * (γ / σ + 2 * D / ε))
    (h2 : ∀ a ∈ Ioo 0 (π / 2),
      h a ≤ c3 * cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (cos a / sin a) ^ 3)
    (hint : IntervalIntegrable (fun a => h a * tan a) volume 0 (π / 2)) :
    (∫ a in (0 : ℝ)..(π / 2), h a * tan a) ≤
      c3 / (6 * σ ^ 3) + sqrt (2 * (1 + κ) * c1 * c3) * (γ / σ + 4 * D / ε) := by
  set c : ℝ := 4 * (1 + κ) * c1 with hcdef
  have hc : 0 < c := by positivity
  set s : ℝ := sqrt (2 * (1 + κ) * c1 * c3) with hsdef
  have hs : 0 < s := sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 2 * (1 + κ) * c1 * c3 := sq_sqrt (by positivity)
  have hcc3 : c * c3 = 2 * s ^ 2 := by rw [hs2, hcdef]; ring
  set t : ℝ := ε * s / c with htdef
  have ht : 0 < t := by positivity
  have hβ0 : 0 < arctan t := arctan_pos.2 ht
  have hβ : arctan t < π / 2 := arctan_lt_pi_div_two _
  have hX : 0 ≤ γ / σ + 2 * D / ε := by positivity
  have hmain := mvbe_integral_mul_tan_le c c3 ε (γ / σ + 2 * D / ε) σ D (arctan t) hc.le hc3.le
    hε hX hσ hD hβ0 hβ h (fun a ha => h1 a ⟨ha.1, lt_of_le_of_lt ha.2 hβ⟩)
    (fun a ha => h2 a ⟨lt_of_lt_of_le hβ0 ha.1, ha.2⟩) hint
  rw [mvbe_cot_eq_inv_tan hβ0 hβ, tan_arctan] at hmain
  refine hmain.trans (le_of_eq ?_)
  rw [htdef]
  field_simp
  linear_combination (6 * σ ^ 3 * D) * hcc3

/-- The optimised form (2.11) with measurability and nonnegativity of `h` in place of the
integrability hypothesis (integrability is obtained from the splitting angle `π/4`). -/
theorem mvbe_keyEstimate_optimised_of_measurable
    (c1 c3 κ γ σ ε D : ℝ) (hc1 : 0 < c1) (hc3 : 0 < c3) (hκ : 0 ≤ κ) (hγ : 0 ≤ γ)
    (hε : 0 < ε) (hσ : 0 < σ) (hD : 0 ≤ D) (h : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable h (volume.restrict (Ioc 0 (π / 2))))
    (hnn : ∀ a ∈ Ioo 0 (π / 2), 0 ≤ h a)
    (h1 : ∀ a ∈ Ioo 0 (π / 2),
      h a ≤ 4 * (1 + κ) * c1 * cos a ^ 2 / (ε * sin a) * (γ / σ + 2 * D / ε))
    (h2 : ∀ a ∈ Ioo 0 (π / 2),
      h a ≤ c3 * cos a ^ 3 / (2 * σ ^ 3) + c3 * D * (cos a / sin a) ^ 3) :
    (∫ a in (0 : ℝ)..(π / 2), h a * tan a) ≤
      c3 / (6 * σ ^ 3) + sqrt (2 * (1 + κ) * c1 * c3) * (γ / σ + 4 * D / ε) := by
  have hpi4 : 0 < π / 4 := by linarith [pi_pos]
  have hpi4' : π / 4 < π / 2 := by linarith [pi_pos]
  exact mvbe_keyEstimate_optimised c1 c3 κ γ σ ε D hc1 hc3 hκ hγ hε hσ hD h h1 h2
    (mvbe_intervalIntegrable_mul_tan (4 * (1 + κ) * c1) c3 ε (γ / σ + 2 * D / ε) σ D (π / 4)
      hc3.le hε hσ hD hpi4 hpi4' h hmeas hnn
      (fun a ha => h1 a ⟨ha.1, lt_of_le_of_lt ha.2 hpi4'⟩)
      (fun a ha => h2 a ⟨lt_of_lt_of_le hpi4 ha.1, ha.2⟩))

/-! ### Part 2: Gaussian tensor integral bounds (Raic Lemma 2.5) -/

/-- `He₁(x) = x`. -/
theorem mvbe_aeval_hermite_one (x : ℝ) : aeval x (hermite 1) = x := by
  simp

theorem mvbe_aeval_hermite_two (x : ℝ) : aeval x (hermite 2) = x ^ 2 - 1 := by
  simp [hermite_succ]
  ring

theorem mvbe_aeval_hermite_three (x : ℝ) : aeval x (hermite 3) = x ^ 3 - 3 * x := by
  simp [hermite_succ]
  ring

theorem mvbe_integrable_pow_gaussianReal (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (X := id) (by simp) n

theorem mvbe_integrable_aeval_gaussianReal (p : ℤ[X]) :
    Integrable (fun t : ℝ => aeval t p) (gaussianReal 0 1) := by
  have : (fun t : ℝ => aeval t p) =
      fun t => ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) * t ^ i := by
    funext t
    rw [aeval_eq_sum_range]
    simp [zsmul_eq_mul]
  rw [this]
  exact integrable_finsetSum _ (fun i _ => (mvbe_integrable_pow_gaussianReal i).const_mul _)

theorem mvbe_integral_cube_gaussianReal : ∫ t : ℝ, t ^ 3 ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  have h := integral_map (μ := gaussianReal 0 1) (φ := fun x : ℝ => -x)
    (f := fun t : ℝ => t ^ 3) (by fun_prop) (by fun_prop)
  rw [hmap] at h
  have h2 : ∫ x : ℝ, (-x) ^ 3 ∂(gaussianReal 0 1) = - ∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 1) := by
    rw [← integral_neg]; congr 1; funext x; ring
  linarith

theorem mvbe_integral_sq_gaussianReal : ∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hv
  simpa using hv

theorem mvbe_stdGaussian_map_inner {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => ⟪z, v⟫) = gaussianReal 0 1 := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin d) => ⟪z, v⟫) = ⇑(innerSL ℝ v) := by
    funext z; rw [innerSL_apply_apply, real_inner_comm]
  rw [hfun, IsGaussian.map_eq_gaussianReal (innerSL ℝ v), integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm, hv]
  simp

/-- The Gaussian constant `c_r = ∫ |He_r| dγ₁` of Raic's Lemmas 2.5 and 2.6. -/
noncomputable def mvbeHermiteConst (r : ℕ) : ℝ :=
  ∫ t : ℝ, |aeval t (hermite r)| ∂(gaussianReal 0 1)

theorem mvbe_integral_aeval_hermite_gaussianReal {r : ℕ} (h1 : 1 ≤ r) (h3 : r ≤ 3) :
    ∫ t : ℝ, aeval t (hermite r) ∂(gaussianReal 0 1) = 0 := by
  interval_cases r
  · simp only [mvbe_aeval_hermite_one]
    exact integral_id_gaussianReal
  · simp only [mvbe_aeval_hermite_two]
    rw [integral_sub (mvbe_integrable_pow_gaussianReal 2) (integrable_const _),
      mvbe_integral_sq_gaussianReal]
    simp
  · simp only [mvbe_aeval_hermite_three]
    have hi : Integrable (fun t : ℝ => 3 * t) (gaussianReal 0 1) := by
      simpa using (mvbe_integrable_pow_gaussianReal 1).const_mul 3
    rw [integral_sub (mvbe_integrable_pow_gaussianReal 3) hi, mvbe_integral_cube_gaussianReal,
      integral_const_mul]
    simp [integral_id_gaussianReal]

/-- Raic's Lemma 2.5 in probabilistic form: the integral of `f` against the Hermite factor
`He_r(⟪z, u⟫ / ‖u‖)` under the standard Gaussian is at most `c_r * M`, where `M` bounds the
oscillation of `f` around a constant `mid`. -/
theorem mvbe_gaussian_hermite_integral_le {d r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ≠ 0) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Measurable f) (mid M : ℝ) (hM : ∀ x, |f x - mid| ≤ M) :
    |∫ z, f z * aeval (⟪z, u⟫ / ‖u‖) (hermite r) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
      ≤ mvbeHermiteConst r * M := by
  set P := stdGaussian (EuclideanSpace ℝ (Fin d)) with hP
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
  set v : EuclideanSpace ℝ (Fin d) := ‖u‖⁻¹ • u with hv
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hun.ne']
  set T : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ⟪z, v⟫ with hT
  have hTm : Measurable T := (continuous_id.inner continuous_const).measurable
  have hTu : ∀ z, ⟪z, u⟫ / ‖u‖ = T z := by
    intro z
    rw [hT, hv]
    simp only [real_inner_smul_right]
    ring
  have hmap : P.map T = gaussianReal 0 1 := mvbe_stdGaussian_map_inner v hvn
  set He : ℝ → ℝ := fun t => aeval t (hermite r) with hHe
  have hHec : Continuous He := (hermite r).continuous_aeval
  have hHeint : Integrable He (P.map T) := by
    rw [hmap]; exact mvbe_integrable_aeval_gaussianReal _
  have hHint : Integrable (fun z => He (T z)) P := hHeint.comp_aemeasurable hTm.aemeasurable
  have hH0 : ∫ z, He (T z) ∂P = 0 := by
    rw [← integral_map hTm.aemeasurable hHec.aestronglyMeasurable, hmap]
    exact mvbe_integral_aeval_hermite_gaussianReal hr1 hr3
  have hHabs : ∫ z, |He (T z)| ∂P = mvbeHermiteConst r := by
    rw [← integral_map hTm.aemeasurable (hHec.abs).aestronglyMeasurable, hmap]
    rfl
  have hfb : ∀ x, ‖f x‖ ≤ M + |mid| := by
    intro x
    have h1 : |f x| ≤ |f x - mid| + |mid| := by
      have := abs_add_le (f x - mid) mid
      simpa using this
    rw [Real.norm_eq_abs]
    linarith [hM x]
  have hfint : Integrable (fun z => f z * He (T z)) P :=
    hHint.bdd_mul hf.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hdint : Integrable (fun z => (f z - mid) * He (T z)) P :=
    hHint.bdd_mul (hf.sub measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa using hM x))
  have hsplit : ∫ z, f z * He (T z) ∂P = ∫ z, (f z - mid) * He (T z) ∂P := by
    have : (fun z => f z * He (T z)) =
        fun z => (f z - mid) * He (T z) + mid * He (T z) := by funext z; ring
    rw [this, integral_add hdint (hHint.const_mul mid), integral_const_mul, hH0, mul_zero,
      add_zero]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hfin : ∫ z, f z * aeval (⟪z, u⟫ / ‖u‖) (hermite r) ∂P = ∫ z, f z * He (T z) ∂P := by
    congr 1; funext z; rw [hTu]
  rw [hfin, hsplit]
  calc |∫ z, (f z - mid) * He (T z) ∂P|
      = ‖∫ z, (f z - mid) * He (T z) ∂P‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, ‖(f z - mid) * He (T z)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ z, M * |He (T z)| ∂P := by
        refine integral_mono hdint.norm (hHint.abs.const_mul M) (fun z => ?_)
        simp only [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hM z) (abs_nonneg _)
    _ = mvbeHermiteConst r * M := by
        rw [integral_const_mul, hHabs]; ring

/-- Raic's Lemma 2.5, scaled form valid for every `u` (the case `u = 0` is trivial since `r ≥ 1`):
`|∫ f(z) He_r(⟪z,u⟫/‖u‖) dγ| ‖u‖^r ≤ c_r M ‖u‖^r`. -/
theorem mvbe_gaussian_hermite_integral_le_scaled {d r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u : EuclideanSpace ℝ (Fin d)) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Measurable f) (mid M : ℝ) (hM : ∀ x, |f x - mid| ≤ M) :
    |∫ z, f z * aeval (⟪z, u⟫ / ‖u‖) (hermite r) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))|
        * ‖u‖ ^ r ≤ mvbeHermiteConst r * M * ‖u‖ ^ r := by
  by_cases hu : u = 0
  · subst hu
    simp [zero_pow (by omega : r ≠ 0)]
  · exact mul_le_mul_of_nonneg_right
      (mvbe_gaussian_hermite_integral_le hr1 hr3 u hu f hf mid M hM) (by positivity)

/-! ### The tensor identity `∇^r φ [u^r] = (-1)^r He_r φ ‖u‖^r` -/

section tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian shape `C exp(-‖w‖²/2)` has Fréchet derivative `-ψ(z) ⟪z, ·⟫` at `z`. -/
theorem mvbe_hasFDerivAt_gaussShape (C : ℝ) (z : E) :
    HasFDerivAt (fun w : E => C * Real.exp (-(‖w‖ ^ 2 / 2)))
      (-(C * Real.exp (-(‖z‖ ^ 2 / 2))) • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (2 • (innerSL ℝ z)) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 : HasFDerivAt (fun w : E => ‖w‖ ^ 2 / 2) ((2 : ℝ)⁻¹ • (2 • (innerSL ℝ z))) z := by
    have := h1.mul_const (2 : ℝ)⁻¹
    simpa only [div_eq_mul_inv, mul_comm ((2 : ℝ)⁻¹)] using this
  have h4 := ((h2.neg).exp).const_mul C
  refine h4.congr_fderiv ?_
  ext w
  simp
  ring

/-- One step of the induction: the directional derivative along `u` of
`(-1)^r He_r(⟪w,u⟫/‖u‖) ‖u‖^r C e^{-‖w‖²/2}` is the same expression with `r + 1`. -/
theorem mvbe_hasFDerivAt_hermite_gauss (C : ℝ) {u : E} (hu : u ≠ 0) (r : ℕ) (z : E) :
    ∃ L : E →L[ℝ] ℝ,
      HasFDerivAt (fun w : E => (-1 : ℝ) ^ r * aeval (⟪w, u⟫ / ‖u‖) (hermite r) * ‖u‖ ^ r
        * (C * Real.exp (-(‖w‖ ^ 2 / 2)))) L z ∧
      L u = (-1 : ℝ) ^ (r + 1) * aeval (⟪z, u⟫ / ‖u‖) (hermite (r + 1)) * ‖u‖ ^ (r + 1)
        * (C * Real.exp (-(‖z‖ ^ 2 / 2))) := by
  have hun : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have ha : HasFDerivAt (fun w : E => ⟪w, u⟫ / ‖u‖) (‖u‖⁻¹ • innerSL ℝ u) z := by
    have h0 : HasFDerivAt (fun w : E => innerSL ℝ u w) (innerSL ℝ u) z :=
      (innerSL ℝ u).hasFDerivAt
    have h1 : HasFDerivAt (fun w : E => innerSL ℝ u w / ‖u‖) (‖u‖⁻¹ • innerSL ℝ u) z := by
      have := h0.mul_const ‖u‖⁻¹
      simpa only [div_eq_mul_inv, mul_comm ‖u‖⁻¹] using this
    have hfun : (fun w : E => ⟪w, u⟫ / ‖u‖) = fun w : E => innerSL ℝ u w / ‖u‖ := by
      funext w; rw [innerSL_apply_apply, real_inner_comm]
    rw [hfun]
    exact h1
  have hH := (Polynomial.hasDerivAt_aeval (q := hermite r) (⟪z, u⟫ / ‖u‖)).comp_hasFDerivAt z ha
  have hψ := mvbe_hasFDerivAt_gaussShape C z
  have hQ := ((hH.const_mul ((-1 : ℝ) ^ r)).mul_const (‖u‖ ^ r)).mul hψ
  refine ⟨_, hQ, ?_⟩
  simp only [add_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply,
    hermite_succ, map_sub, map_mul, aeval_X, real_inner_self_eq_norm_sq]
  simp only [Function.comp_apply]
  field_simp
  ring

theorem mvbe_contDiff_gaussShape (C : ℝ) :
    ContDiff ℝ ⊤ (fun w : E => C * Real.exp (-(‖w‖ ^ 2 / 2))) := by
  have h1 : ContDiff ℝ ⊤ (fun w : E => ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  exact contDiff_const.mul (Real.contDiff_exp.comp (h1.div_const 2).neg)

/-- The tensor identity: the `r`-th derivative of the Gaussian shape applied to `u ⊗ ⋯ ⊗ u`
is `(-1)^r He_r(⟪z,u⟫/‖u‖) ‖u‖^r` times the shape. -/
theorem mvbe_iteratedFDeriv_gaussShape (C : ℝ) (u z : E) (r : ℕ) :
    iteratedFDeriv ℝ r (fun w : E => C * Real.exp (-(‖w‖ ^ 2 / 2))) z (fun _ => u) =
      (-1 : ℝ) ^ r * aeval (⟪z, u⟫ / ‖u‖) (hermite r) * ‖u‖ ^ r
        * (C * Real.exp (-(‖z‖ ^ 2 / 2))) := by
  by_cases hu : u = 0
  · subst hu
    cases r with
    | zero => simp [iteratedFDeriv_zero_apply]
    | succ r =>
        have : (iteratedFDeriv ℝ (r + 1) (fun w : E => C * Real.exp (-(‖w‖ ^ 2 / 2))) z)
            (fun _ => (0 : E)) = 0 :=
          ContinuousMultilinearMap.map_coord_zero _ (0 : Fin (r + 1)) rfl
        rw [this]
        simp
  · induction r generalizing z with
    | zero => simp [iteratedFDeriv_zero_apply]
    | succ r ih =>
        have hdiff : DifferentiableAt ℝ
            (iteratedFDeriv ℝ r (fun w : E => C * Real.exp (-(‖w‖ ^ 2 / 2)))) z :=
          ((mvbe_contDiff_gaussShape (E := E) C).differentiable_iteratedFDeriv
            (by exact_mod_cast WithTop.coe_lt_top (r : ℕ∞))) z
        obtain ⟨L, hL, hLu⟩ := mvbe_hasFDerivAt_hermite_gauss C hu r z
        have hfun : (fun y => iteratedFDeriv ℝ r
            (fun w : E => C * Real.exp (-(‖w‖ ^ 2 / 2))) y (fun _ => u)) =
            fun w : E => (-1 : ℝ) ^ r * aeval (⟪w, u⟫ / ‖u‖) (hermite r) * ‖u‖ ^ r
              * (C * Real.exp (-(‖w‖ ^ 2 / 2))) := by
          funext y; exact ih y
        rw [iteratedFDeriv_succ_apply_left]
        have h2 := fderiv_continuousMultilinear_apply_const_apply hdiff (fun _ : Fin r => u) u
        rw [hfun, hL.fderiv] at h2
        rw [← hLu]
        exact h2.symm

end tensor

/-! ### The density of the standard Gaussian, and Lemma 2.5 in the paper's form -/

section density

/-- Tonelli in `n` variables for a product of one-variable functions. -/
theorem mvbe_lintegral_fin_prod {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] {ν : (i : Fin n) → Measure (X i)} [∀ i, SigmaFinite (ν i)]
    (f : (i : Fin n) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → X i, ∏ i, f i (x i) ∂(Measure.pi ν) = ∏ i, ∫⁻ x, f i x ∂(ν i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hF : Measurable fun x : (i : Fin (n + 1)) → X i => ∏ i, f i (x i) :=
        Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
      have hg : Measurable fun y : (i : Fin n) → X (Fin.succ i) =>
          ∏ i : Fin n, f (Fin.succ i) (y i) :=
        Finset.measurable_prod _ fun i _ => (hf _).comp (measurable_pi_apply i)
      calc ∫⁻ x : (i : Fin (n + 1)) → X i, ∏ i, f i (x i) ∂(Measure.pi ν)
          = ∫⁻ p : X 0 × ((i : Fin n) → X (Fin.succ i)),
              f 0 p.1 * ∏ i : Fin n, f (Fin.succ i) (p.2 i)
              ∂((ν 0).prod (Measure.pi fun i => ν i.succ)) := by
            rw [← ((measurePreserving_piFinSuccAbove ν 0).symm).lintegral_comp hF]
            simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
              Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
              Fin.zero_succAbove, cast_eq, Fin.cons_zero]
            rfl
        _ = (∫⁻ x, f 0 x ∂(ν 0))
              * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(ν i.succ) := by
            rw [lintegral_prod_mul (f := f 0)
              (g := fun y : (i : Fin n) → X (Fin.succ i) => ∏ i : Fin n, f (Fin.succ i) (y i))
              (hf 0).aemeasurable hg.aemeasurable,
              ih (fun i => f (Fin.succ i)) fun i => hf _]
        _ = ∏ i, ∫⁻ x, f i x ∂(ν i) := by rw [Fin.prod_univ_succ]

/-- A product of measures given by densities has the product density. -/
theorem mvbe_pi_withDensity_prod {n : ℕ} (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i))] :
    Measure.pi (fun i => (volume : Measure ℝ).withDensity (f i))
      = (volume : Measure (Fin n → ℝ)).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  refine (Measure.pi_eq (μ := fun i => (volume : Measure ℝ).withDensity (f i))
    (μ' := (volume : Measure (Fin n → ℝ)).withDensity fun x => ∏ i, f i (x i)) fun s hs => ?_)
  have hF : Measurable fun x : Fin n → ℝ => ∏ i, f i (x i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hpt : ∀ x : Fin n → ℝ,
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x
        = ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra hcon
        push Not at hcon
        exact hx fun i _ => hcon i
      exact (Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem hi (f i))).symm
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox, lintegral_congr hpt,
    volume_pi, mvbe_lintegral_fin_prod (ν := fun _ => (volume : Measure ℝ))
      (fun i => (s i).indicator (f i)) fun i => (hf i).indicator (hs i)]
  exact Finset.prod_congr rfl fun i _ => by
    rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

/-- The product of `n` standard Gaussians on `Fin n → ℝ` has the product density. -/
theorem mvbe_pi_gaussianReal_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)
      = (volume : Measure (Fin n → ℝ)).withDensity fun x => ∏ i, gaussianPDF 0 1 (x i) := by
  haveI hprob : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]
    infer_instance
  have hpi : Measure.pi (fun _ : Fin n => gaussianReal 0 1)
      = Measure.pi fun _ : Fin n => (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    congr 1
    funext i
    exact gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [hpi]
  exact mvbe_pi_withDensity_prod (fun _ : Fin n => gaussianPDF 0 1)
    (fun _ => measurable_gaussianPDF 0 1)

/-- Pushing a density forward along a measure preserving equivalence. -/
theorem mvbe_map_withDensity_measurePreserving {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β)
    (he : MeasurePreserving e μ ν) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g).map e = ν.withDensity fun y => g (e.symm y) := by
  ext T hT
  rw [Measure.map_apply e.measurable hT, withDensity_apply _ (e.measurable hT),
    withDensity_apply _ hT, ← lintegral_indicator (e.measurable hT), ← lintegral_indicator hT]
  have key : ∫⁻ a, T.indicator (fun y => g (e.symm y)) (e a) ∂μ
      = ∫⁻ b, T.indicator (fun y => g (e.symm y)) b ∂ν :=
    he.lintegral_comp ((hg.comp e.symm.measurable).indicator hT)
  rw [← key]
  refine lintegral_congr fun x => ?_
  by_cases hx : e x ∈ T
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ e ⁻¹' T from hx)]
    simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ e ⁻¹' T from hx)]

/-- The standard Gaussian on `EuclideanSpace ℝ (Fin d)` has the product density. -/
theorem mvbe_stdGaussian_eq_withDensity_prod (d : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
      = (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
          fun y => ∏ i, gaussianPDF 0 1 (y i) := by
  have hmeas : Measurable fun x : Fin d → ℝ => ∏ i, gaussianPDF 0 1 (x i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have hmp : MeasurePreserving ⇑(MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (volume : Measure (Fin d → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    PiLp.volume_preserving_toLp (Fin d)
  rw [← map_pi_eq_stdGaussian, mvbe_pi_gaussianReal_eq_withDensity]
  exact mvbe_map_withDensity_measurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ)) hmp hmeas

/-- The density `φ_d(z) = (2π)^{-d/2} e^{-‖z‖²/2}` of the standard Gaussian on `ℝ^d`
(written with `(√(2π))⁻¹ ^ d`). -/
noncomputable def mvbeGaussDensity (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ((√(2 * π))⁻¹) ^ d * Real.exp (-(‖z‖ ^ 2 / 2))

theorem mvbe_continuous_gaussDensity (d : ℕ) : Continuous (mvbeGaussDensity d) := by
  unfold mvbeGaussDensity; fun_prop

theorem mvbeGaussDensity_nonneg (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    0 ≤ mvbeGaussDensity d z := by
  unfold mvbeGaussDensity; positivity

theorem mvbe_prod_gaussianPDF_eq (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) :
    ∏ i, gaussianPDF 0 1 (y i) = ENNReal.ofReal (mvbeGaussDensity d y) := by
  unfold gaussianPDF
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg 0 1 _)]
  congr 1
  unfold gaussianPDFReal mvbeGaussDensity
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

/-- The standard Gaussian on `ℝ^d` has density `φ_d` with respect to Lebesgue measure. -/
theorem mvbe_stdGaussian_eq_withDensity (d : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin d))
      = (volume : Measure (EuclideanSpace ℝ (Fin d))).withDensity
          fun y => ENNReal.ofReal (mvbeGaussDensity d y) := by
  rw [mvbe_stdGaussian_eq_withDensity_prod]
  congr 1
  funext y
  exact mvbe_prod_gaussianPDF_eq d y

/-- Integrals against `φ_d dz` are integrals against the standard Gaussian. -/
theorem mvbe_integral_mul_gaussDensity (d : ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ z, mvbeGaussDensity d z * g z ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))
      = ∫ z, g z ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have hm : Measurable fun y : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (mvbeGaussDensity d y) :=
    ENNReal.measurable_ofReal.comp (mvbe_continuous_gaussDensity d).measurable
  rw [mvbe_stdGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul hm (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp [ENNReal.toReal_ofReal (mvbeGaussDensity_nonneg d z)]

/-- The `r`-th derivative of `φ_d` applied to `u ⊗ ⋯ ⊗ u`, in the paper's normalisation. -/
theorem mvbe_iteratedFDeriv_gaussDensity (d r : ℕ) (u z : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ r (mvbeGaussDensity d) z (fun _ => u) =
      (-1 : ℝ) ^ r * aeval (⟪z, u⟫ / ‖u‖) (hermite r) * ‖u‖ ^ r * mvbeGaussDensity d z :=
  mvbe_iteratedFDeriv_gaussShape (((√(2 * π))⁻¹) ^ d) u z r

/-- **Raic's Lemma 2.5**, in the paper's form `|∫ f ⟨∇^r φ_d, u^{⊗r}⟩ dz| ≤ c_r M₀*(f) ‖u‖^r`
for `r ∈ {1, 2, 3}`; here `M₀*(f)` is replaced by any `M` with `|f - mid| ≤ M` (the midrange
choice `mid = (inf f + sup f)/2` gives `M = M₀*(f)`). -/
theorem mvbe_lemma_2_5 {d r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u : EuclideanSpace ℝ (Fin d)) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (mid M : ℝ) (hM : ∀ x, |f x - mid| ≤ M) :
    |∫ z, f z * iteratedFDeriv ℝ r (mvbeGaussDensity d) z (fun _ => u)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d)))|
      ≤ mvbeHermiteConst r * M * ‖u‖ ^ r := by
  by_cases hu : u = 0
  · subst hu
    simp [mvbe_iteratedFDeriv_gaussDensity, zero_pow (by omega : r ≠ 0)]
  · have hform : ∀ z, f z * iteratedFDeriv ℝ r (mvbeGaussDensity d) z (fun _ => u)
        = ((-1 : ℝ) ^ r * ‖u‖ ^ r) *
          (mvbeGaussDensity d z * (f z * aeval (⟪z, u⟫ / ‖u‖) (hermite r))) := by
      intro z
      rw [mvbe_iteratedFDeriv_gaussDensity]
      ring
    simp_rw [hform]
    rw [integral_const_mul, mvbe_integral_mul_gaussDensity d
      (fun z => f z * aeval (⟪z, u⟫ / ‖u‖) (hermite r)), abs_mul]
    have hb := mvbe_gaussian_hermite_integral_le hr1 hr3 u hu f hf mid M hM
    have hn : |(-1 : ℝ) ^ r * ‖u‖ ^ r| = ‖u‖ ^ r := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_norm]
    rw [hn]
    calc ‖u‖ ^ r * |∫ z, f z * aeval (⟪z, u⟫ / ‖u‖) (hermite r)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))| ≤ ‖u‖ ^ r * (mvbeHermiteConst r * M) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = mvbeHermiteConst r * M * ‖u‖ ^ r := by ring

end density

end LatticeProb

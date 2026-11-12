import LatticeProb.LQG.GMCScaleIncrement

/-!
# The scale-ratio `L¹` increment bound, uniformly over whole-plane Gaussian free fields

For `0 < γ < 2`, a continuous compactly supported weight `g` and a radius `R > 0` with `‖z‖ + 1 ≤ R` on the
support of `g`, there are constants `K ≥ 0` and `c > 0`, depending only on `γ`, `g` and `R`, such that for every
whole-plane Gaussian free field with circle averages `h_r(z)`, all `0 < ε ≤ 1` and `ε / 2 ≤ s ≤ ε`,
`E |∫ g(z) (s^{γ²/2} e^{γ (h_s(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}) dz| ≤ K ε^c`.

This is the bound of `scaleIncrementL1Bound_of_isWholePlaneGFF` with the quantifier over the field moved inside
the constants: the bound used there depends on the field only through its covariance. The uniform form is needed
when the bound is applied to a sequence of fields, such as the dilations `h(2^{-j} ·) - h_{2^{-j}}(0)`.

## Main results

* `LatticeProb.Gauss.exists_scaleIncrement_bound_uniform`.
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

universe u

namespace LatticeProb.Gauss

/-- **Uniform scale-ratio `L¹` increment bound.** For `0 < γ < 2`, a continuous compactly supported `g` and
`R > 0` with `‖z‖ + 1 ≤ R` on the support of `g`, there are `K ≥ 0` and `c > 0` such that for every whole-plane
Gaussian free field, all `0 < ε ≤ 1` and `ε / 2 ≤ s ≤ ε`,
`E |∫ g(z) (s^{γ²/2} e^{γ (h_s(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}) dz| ≤ K ε^c`. -/
theorem exists_scaleIncrement_bound_uniform {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}, IsWholePlaneGFF P hC hcirc →
      ∀ ε s : ℝ, 0 < ε → ε ≤ 1 → ε / 2 ≤ s → s ≤ ε →
        ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
          ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤ K * ε ^ c := by
  obtain ⟨C, hCb⟩ := hgc.bounded_above_of_compact_support hgs
  have hCa : ∀ z, |g z| ≤ C := fun z => by simpa [Real.norm_eq_abs] using hCb z
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hCa 0)
  have hg : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hgm : Measurable g := hgc.measurable
  obtain ⟨α, hγα, hα, hb, hd⟩ : ∃ α : ℝ, γ ≤ α ∧ α ≤ 2 * γ ∧ 0 < (2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 ∧
      0 < (α - γ) ^ 2 / 2 := by
    rcases lt_or_ge γ 1 with h1 | h1
    · exact ⟨2 * γ, by linarith, le_rfl, by nlinarith, by nlinarith⟩
    · exact ⟨2, by linarith, by linarith, by nlinarith, by nlinarith⟩
  set b : ℝ := (2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 with hbdef
  set d : ℝ := (α - γ) ^ 2 / 2 with hddef
  have hI0 : 0 ≤ ∫ z, |g z| := integral_nonneg fun _ => abs_nonneg _
  have hB0 : 0 ≤ rexp (γ ^ 2 * Real.log 2) - 1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  set A1 : ℝ := ((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log R * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
      (C * π * 4 * ∫ z, |g z|) + 1) / 2 with hA1
  set A2 : ℝ := 2 * (∫ z, |g z|) * rexp (Real.log R * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) with hA2
  have hA10 : 0 ≤ A1 := by
    refine div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hB0 (Real.exp_pos _).le)
      (mul_nonneg (mul_nonneg (mul_nonneg hC0 Real.pi_pos.le) (by norm_num)) hI0)) zero_le_one) zero_le_two
  have hA20 : 0 ≤ A2 := mul_nonneg (mul_nonneg zero_le_two hI0) (Real.exp_pos _).le
  have hpt : ∀ x, min b d ≤ x → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → rexp (Real.log ε * x) ≤ ε ^ min b d :=
    fun x hx ε hε hε1 => by
      rw [← Real.rpow_def_of_pos hε]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 hx
  refine ⟨A1 + A2, min b d, add_nonneg hA10 hA20, lt_min hb hd, fun {Ω} _ {P} {hC} {hcirc} hh ε s hε hε1 hs2 hsε => ?_⟩
  have hs : 0 < s := lt_of_lt_of_le (half_pos hε) hs2
  have hgε : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R := fun z hz => by linarith [hsupp z hz]
  refine (hh.integral_abs_integral_increment_le_exp_of_le hs hsε hs2 hR hgm hg hCa hgε hγα hα).trans ?_
  calc _ ≤ A1 * ε ^ min b d + A2 * ε ^ min b d :=
        add_le_add (mul_le_mul_of_nonneg_left (hpt b (min_le_left _ _) ε hε hε1) hA10)
          (mul_le_mul_of_nonneg_left (hpt d (min_le_right _ _) ε hε hε1) hA20)
    _ = _ := by ring

end LatticeProb.Gauss

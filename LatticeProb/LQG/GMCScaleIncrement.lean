import LatticeProb.LQG.GMCL1RateLe

/-!
# The scale-ratio `L¹` increment bound for the whole-plane Gaussian free field

For a whole-plane Gaussian free field with circle averages `h_r(z)` and `0 < γ < 2`, every continuous compactly
supported weight `g` satisfies, for suitable `R`, `K` and `c > 0` and all `0 < ε ≤ 1` and `ε / 2 ≤ s ≤ ε`,
`E |∫ g(z) (s^{γ²/2} e^{γ (h_s(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}) dz| ≤ K ε^c`.

## Main results

* `scaleIncrementL1Bound_of_isWholePlaneGFF`: the bound `ScaleIncrementL1Bound P γ hcirc` for every whole-plane
  Gaussian free field and every `0 < γ < 2`. The thick-point level is `α = 2γ` for `γ < 1` and `α = 2` for
  `1 ≤ γ < 2`, and the exponent is `c = min (b / 2) ((α - γ)² / 2)`, `b = 2 - γ² + (2γ - α)²/2`.
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **The scale-ratio `L¹` increment bound holds for every whole-plane Gaussian free field** and `0 < γ < 2`. -/
theorem scaleIncrementL1Bound_of_isWholePlaneGFF (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) : ScaleIncrementL1Bound P γ hcirc := by
  intro g hgc hgs
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hgs.isCompact.isBounded
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
  set R : ℝ := max R0 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hsupp : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R := fun z hz => by
    have h1 : ‖z‖ ≤ R0 := mem_closedBall_zero_iff.mp (hR0 (subset_tsupport g hz))
    linarith [le_max_left R0 0]
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
  refine ⟨R, A1 + A2, min b d, hR, lt_min hb hd, hsupp, fun ε s hε hε1 hs2 hsε => ?_⟩
  have hs : 0 < s := lt_of_lt_of_le (half_pos hε) hs2
  have hgε : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R := fun z hz => by linarith [hsupp z hz]
  refine (hh.integral_abs_integral_increment_le_exp_of_le hs hsε hs2 hR hgm hg hCa hgε hγα hα).trans ?_
  calc _ ≤ A1 * ε ^ min b d + A2 * ε ^ min b d :=
        add_le_add (mul_le_mul_of_nonneg_left (hpt b (min_le_left _ _) ε hε hε1) hA10)
          (mul_le_mul_of_nonneg_left (hpt d (min_le_right _ _) ε hε hε1) hA20)
    _ = _ := by ring

end LatticeProb.Gauss

import LatticeProb.LQG.GMCThickPart
import LatticeProb.LQG.GMCPointwiseMomentsLe

/-!
# Thick points of the circle-average approximations at a general scale ratio

This is the version of `LatticeProb.LQG.GMCThickPart` for the increment `D_z = h_s(z) - h_ε(z)` between the circle
averages of radii `s` and `ε`, for arbitrary `0 < s ≤ ε`, instead of the dyadic increment `s = ε / 2`.
With `X_z = h_ε(z) - h_R(0)` and `L = log (R / ε)`, and a measurable weight `g ≥ 0` supported where `‖z‖ + ε ≤ R`:

* `lintegral_lintegral_thick_mul_exp_incr_le`:
  `E ∫ g(z) e^{γ X_z} 1{X_z ≥ α L} e^{γ D_z} dν(z) ≤ (∫ g dν) (ε / s)^{γ²/2} e^{L (γ²/2 - (α - γ)²/2)}`.

The other thick-point estimate of `GMCThickPart` (`lintegral_lintegral_thick_le`) does not involve the increment and
is used as it stands.
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

namespace LatticeProb.Gauss.IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Thick points of the finer approximation, integrated over the plane: with `D_z = h_s(z) - h_ε(z)`,
`E ∫ g(z) e^{γ X_z} 1{X_z ≥ α L} e^{γ D_z} dν(z) ≤ (∫ g dν) e^{γ² log (ε / s) / 2} e^{L (γ²/2 - (α - γ)²/2)}`. -/
theorem lintegral_lintegral_thick_mul_exp_incr_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ}
    (hs : 0 < s) (hsε : s ≤ ε) (hR : 0 < R) {γ α : ℝ} (hγα : γ ≤ α) (ν : Measure ℂ) [SFinite ν]
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (hgs : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) :
    ∫⁻ ω, ∫⁻ z, g z * ENNReal.ofReal ((Set.Ici (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
        (hcirc ω ε z - hcirc ω R 0) * rexp (γ * (hcirc ω s z - hcirc ω ε z))) ∂ν ∂P ≤
      (∫⁻ z, g z ∂ν) * (ENNReal.ofReal (rexp (γ ^ 2 * Real.log (ε / s) / 2)) *
        ENNReal.ofReal (rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) := by
  have := hh.isProbabilityMeasure
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  set I : ℝ → ℝ := (Set.Ici (α * Real.log (R / ε))).indicator fun x => rexp (γ * x) with hIdef
  have hI : Measurable I := (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Ici
  have hI0 : ∀ x, 0 ≤ I x := fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  have hF : Measurable (uncurry fun (z : ℂ) (p : ℝ × ℝ × ℝ) =>
      g z * ENNReal.ofReal (I (p.2.1 - p.2.2) * rexp (γ * (p.1 - p.2.1)))) :=
    (hg.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp
      ((hI.comp ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))).mul
        (by fun_prop)))
  have hlog : ((Real.log (ε / s)).toNNReal : ℝ) = Real.log (ε / s) :=
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hs).mpr hsε))
  calc ∫⁻ ω, ∫⁻ z, g z * ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
          rexp (γ * (hcirc ω s z - hcirc ω ε z))) ∂ν ∂P
      = ∫⁻ z, ∫⁻ ω, g z * ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
          rexp (γ * (hcirc ω s z - hcirc ω ε z))) ∂P ∂ν :=
        hh.lintegral_lintegral_circle_swap
          (F := fun z p => g z * ENNReal.ofReal (I (p.2.1 - p.2.2) * rexp (γ * (p.1 - p.2.1))))
          hs hε hR ν hF
    _ ≤ ∫⁻ z, g z * (ENNReal.ofReal (rexp (γ ^ 2 * Real.log (ε / s) / 2)) *
          ENNReal.ofReal (rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) ∂ν := by
        refine lintegral_mono fun z => ?_
        by_cases hz0 : g z = 0
        · simp [hz0]
        have hz := hgs z hz0
        have hεR : ε ≤ R := by linarith [norm_nonneg z]
        have hL : ((Real.log (R / ε)).toNNReal : ℝ) = Real.log (R / ε) :=
          Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hε).mpr hεR))
        have hXm : Measurable fun ω => hcirc ω ε z - hcirc ω R 0 :=
          (hh.measurable_circle ε z hε).sub (hh.measurable_circle R 0 hR)
        have hDm : Measurable fun ω => hcirc ω s z - hcirc ω ε z :=
          (hh.measurable_circle s z hs).sub (hh.measurable_circle ε z hε)
        have hA : Measurable fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)) :=
          ENNReal.measurable_ofReal.comp (hI.comp hXm)
        have hB : Measurable fun ω => ENNReal.ofReal (rexp (γ * (hcirc ω s z - hcirc ω ε z))) :=
          ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).comp hDm)
        have hind : IndepFun (fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)))
            (fun ω => ENNReal.ofReal (rexp (γ * (hcirc ω s z - hcirc ω ε z)))) P :=
          (hh.indepFun_recentred_incr_le hs hsε hz).comp (ENNReal.measurable_ofReal.comp hI)
            (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)))
        have hsplit : ∀ ω, ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
            rexp (γ * (hcirc ω s z - hcirc ω ε z))) =
            (fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)) *
              ENNReal.ofReal (rexp (γ * (hcirc ω s z - hcirc ω ε z)))) ω :=
          fun ω => ENNReal.ofReal_mul (hI0 _)
        have hAB : Measurable fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
            rexp (γ * (hcirc ω s z - hcirc ω ε z))) :=
          ENNReal.measurable_ofReal.comp ((hI.comp hXm).mul
            ((by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).comp hDm))
        rw [lintegral_const_mul (g z) hAB]
        gcongr
        rw [lintegral_congr hsplit]
        have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hA hB hind
        simp only [Pi.mul_apply] at hmul ⊢
        rw [hmul, mul_comm]
        have hexp := GaussTail.lintegral_ofReal_exp_mul_of_hasLaw (hh.hasLaw_incr_le hs hsε z) γ
        rw [hlog] at hexp
        rw [hexp]
        gcongr
        have h := GaussTail.lintegral_ofReal_indicator_Ici_exp_mul_le_of_hasLaw
          (hh.hasLaw_recentred_circle hε hz) hγα
        rw [hL] at h
        exact h
    _ = _ := lintegral_mul_const _ hg

end LatticeProb.Gauss.IsWholePlaneGFF

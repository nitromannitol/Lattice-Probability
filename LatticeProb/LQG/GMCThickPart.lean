import LatticeProb.LQG.GMCPointwiseMoments
import LatticeProb.LQG.LQGMeasureLocality

/-!
# Thick points of the circle-average approximations of Gaussian multiplicative chaos

Let `h` be a whole-plane GFF with circle averages `h_r(z)`, and write `X_z = h_ε(z) - h_R(0)`,
`D_z = h_{ε/2}(z) - h_ε(z)` and `L = log (R / ε)`. For a measurable weight `g ≥ 0` supported where `‖z‖ + ε ≤ R`,
this file integrates the pointwise thick-point bounds of `LatticeProb.LQG.GMCPointwiseMoments` over the plane
(the first half of the truncated second-moment method of Duplantier-Sheffield 2011, Section 3):

* `lintegral_lintegral_thick_le`: `E ∫ g(z) e^{γ X_z} 1{X_z ≥ α L} dν(z) ≤ (∫ g dν) e^{L (γ²/2 - (α - γ)²/2)}`;
* `lintegral_lintegral_thick_mul_exp_increment_le`: the same for `e^{γ X_z} e^{γ D_z} 1{X_z ≥ α L}` with the extra factor
  `2^{γ²/2} = e^{γ² log 2 / 2}`.

The exchange of `E` and `∫ dν` (`lintegral_lintegral_circle_swap`) goes through the jointly measurable modification of
the circle-average process.
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

namespace LatticeProb.GaussTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- Upper-truncated exponential moment of a `N(0, L)` random variable, as a lower Lebesgue integral. -/
theorem lintegral_ofReal_indicator_Ici_exp_mul_le_of_hasLaw {L : ℝ≥0} (hX : HasLaw X (gaussianReal 0 L) P)
    {t α : ℝ} (htα : t ≤ α) :
    ∫⁻ ω, ENNReal.ofReal ((Set.Ici (α * L)).indicator (fun x => rexp (t * x)) (X ω)) ∂P ≤
      ENNReal.ofReal (rexp (L * (t ^ 2 / 2 - (α - t) ^ 2 / 2))) := by
  have hint : Integrable ((Set.Ici (α * (L : ℝ))).indicator fun x => rexp (t * x)) (gaussianReal 0 L) :=
    (integrable_exp_mul_gaussianReal t).indicator measurableSet_Ici
  have hm : Measurable ((Set.Ici (α * (L : ℝ))).indicator fun x => rexp (t * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (t * x)).indicator measurableSet_Ici
  calc ∫⁻ ω, ENNReal.ofReal ((Set.Ici (α * L)).indicator (fun x => rexp (t * x)) (X ω)) ∂P
      = ∫⁻ x, ENNReal.ofReal ((Set.Ici (α * L)).indicator (fun x => rexp (t * x)) x) ∂(gaussianReal 0 L) :=
        hX.lintegral_comp (ENNReal.measurable_ofReal.comp hm).aemeasurable
    _ = ENNReal.ofReal (∫ x, (Set.Ici (α * L)).indicator (fun x => rexp (t * x)) x ∂(gaussianReal 0 L)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x)).symm
    _ ≤ _ := by
        rw [integral_indicator measurableSet_Ici]
        exact ENNReal.ofReal_le_ofReal (setIntegral_Ici_exp_mul_gaussianReal_le_scale L htα)

/-- The exponential moment of a `N(0, v)` random variable, as a lower Lebesgue integral. -/
theorem lintegral_ofReal_exp_mul_of_hasLaw {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (rexp (t * X ω)) ∂P = ENNReal.ofReal (rexp (t ^ 2 * v / 2)) := by
  calc ∫⁻ ω, ENNReal.ofReal (rexp (t * X ω)) ∂P
      = ∫⁻ x, ENNReal.ofReal (rexp (t * x)) ∂(gaussianReal 0 v) :=
        hX.lintegral_comp (f := fun x => ENNReal.ofReal (rexp (t * x))) (by fun_prop)
    _ = ENNReal.ofReal (∫ x, rexp (t * x) ∂(gaussianReal 0 v)) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal t)
          (ae_of_all _ fun x => (Real.exp_pos _).le)).symm
    _ = _ := by
        rw [integral_exp_mul_gaussianReal_zero]
        congr 2
        ring

end LatticeProb.GaussTail

namespace LatticeProb.Gauss.IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Tonelli for functionals of the circle averages: `E ∫ F(z, h_r(z), h_s(z), h_R(0)) dν(z)
= ∫ E F(z, h_r(z), h_s(z), h_R(0)) dν(z)` for every measurable `F ≥ 0`. -/
theorem lintegral_lintegral_circle_swap (hh : IsWholePlaneGFF P hC hcirc) {r s R : ℝ} (hr : 0 < r)
    (hs : 0 < s) (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {F : ℂ → ℝ × ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable (uncurry F)) :
    ∫⁻ ω, ∫⁻ z, F z (hcirc ω r z, hcirc ω s z, hcirc ω R 0) ∂ν ∂P =
      ∫⁻ z, ∫⁻ ω, F z (hcirc ω r z, hcirc ω s z, hcirc ω R 0) ∂P ∂ν := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have e1 : ∫⁻ ω, ∫⁻ z, F z (hcirc ω r z, hcirc ω s z, hcirc ω R 0) ∂ν ∂P =
      ∫⁻ ω, ∫⁻ z, F z (H ω r z, H ω s z, H ω R 0) ∂ν ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hHae] with ω hω
    simp only [hω]
  have e2 : ∀ z, ∫⁻ ω, F z (H ω r z, H ω s z, H ω R 0) ∂P =
      ∫⁻ ω, F z (hcirc ω r z, hcirc ω s z, hcirc ω R 0) ∂P := by
    intro z
    refine lintegral_congr_ae ?_
    filter_upwards [hHae] with ω hω
    simp only [hω]
  have hm1 : Measurable fun p : Ω × ℂ => H p.1 r p.2 := (hHm r hr).comp measurable_swap
  have hm2 : Measurable fun p : Ω × ℂ => H p.1 s p.2 := (hHm s hs).comp measurable_swap
  have hm3 : Measurable fun p : Ω × ℂ => H p.1 R 0 :=
    (hHm R hR).comp (measurable_const.prodMk measurable_fst)
  have hmeas : Measurable (uncurry fun ω z => F z (H ω r z, H ω s z, H ω R 0)) :=
    hF.comp (measurable_snd.prodMk (hm1.prodMk (hm2.prodMk hm3)))
  rw [e1, lintegral_lintegral_swap hmeas.aemeasurable]
  exact lintegral_congr e2

/-- Thick points, integrated over the plane: for a measurable weight `g ≥ 0` supported where `‖z‖ + ε ≤ R` and
`γ ≤ α`, `E ∫ g(z) e^{γ X_z} 1{X_z ≥ α L} dν(z) ≤ (∫ g dν) e^{L (γ²/2 - (α - γ)²/2)}`, `L = log (R / ε)`. -/
theorem lintegral_lintegral_thick_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    {γ α : ℝ} (hγα : γ ≤ α) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hgs : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) :
    ∫⁻ ω, ∫⁻ z, g z * ENNReal.ofReal ((Set.Ici (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
        (hcirc ω ε z - hcirc ω R 0)) ∂ν ∂P ≤
      (∫⁻ z, g z ∂ν) * ENNReal.ofReal (rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2))) := by
  set I : ℝ → ℝ := (Set.Ici (α * Real.log (R / ε))).indicator fun x => rexp (γ * x) with hIdef
  have hI : Measurable I := (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Ici
  have hF : Measurable (uncurry fun (z : ℂ) (p : ℝ × ℝ × ℝ) => g z * ENNReal.ofReal (I (p.2.1 - p.2.2))) :=
    (hg.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp
      (hI.comp ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))))
  calc ∫⁻ ω, ∫⁻ z, g z * ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)) ∂ν ∂P
      = ∫⁻ z, ∫⁻ ω, g z * ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)) ∂P ∂ν :=
        hh.lintegral_lintegral_circle_swap (F := fun z p => g z * ENNReal.ofReal (I (p.2.1 - p.2.2))) hε hε hR ν hF
    _ ≤ ∫⁻ z, g z * ENNReal.ofReal (rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2))) ∂ν := by
        refine lintegral_mono fun z => ?_
        by_cases hz0 : g z = 0
        · simp [hz0]
        have hz := hgs z hz0
        have hεR : ε ≤ R := by linarith [norm_nonneg z]
        have hL : ((Real.log (R / ε)).toNNReal : ℝ) = Real.log (R / ε) :=
          Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hε).mpr hεR))
        have hXm : Measurable fun ω => hcirc ω ε z - hcirc ω R 0 :=
          (hh.measurable_circle ε z hε).sub (hh.measurable_circle R 0 hR)
        have hA : Measurable fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)) :=
          ENNReal.measurable_ofReal.comp (hI.comp hXm)
        rw [lintegral_const_mul (g z) hA]
        gcongr
        have h := GaussTail.lintegral_ofReal_indicator_Ici_exp_mul_le_of_hasLaw
          (hh.hasLaw_recentred_circle hε hz) hγα
        rw [hL] at h
        exact h
    _ = _ := lintegral_mul_const _ hg

/-- Thick points of the finer approximation, integrated over the plane: with `D_z = h_{ε/2}(z) - h_ε(z)`,
`E ∫ g(z) e^{γ X_z} 1{X_z ≥ α L} e^{γ D_z} dν(z) ≤ (∫ g dν) e^{γ² log 2 / 2} e^{L (γ²/2 - (α - γ)²/2)}`. -/
theorem lintegral_lintegral_thick_mul_exp_increment_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) {γ α : ℝ} (hγα : γ ≤ α) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) (hgs : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) :
    ∫⁻ ω, ∫⁻ z, g z * ENNReal.ofReal ((Set.Ici (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
        (hcirc ω ε z - hcirc ω R 0) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z))) ∂ν ∂P ≤
      (∫⁻ z, g z ∂ν) * (ENNReal.ofReal (rexp (γ ^ 2 * Real.log 2 / 2)) *
        ENNReal.ofReal (rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) := by
  have := hh.isProbabilityMeasure
  set I : ℝ → ℝ := (Set.Ici (α * Real.log (R / ε))).indicator fun x => rexp (γ * x) with hIdef
  have hI : Measurable I := (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Ici
  have hI0 : ∀ x, 0 ≤ I x := fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  have hF : Measurable (uncurry fun (z : ℂ) (p : ℝ × ℝ × ℝ) =>
      g z * ENNReal.ofReal (I (p.2.1 - p.2.2) * rexp (γ * (p.1 - p.2.1)))) :=
    (hg.comp measurable_fst).mul (ENNReal.measurable_ofReal.comp
      ((hI.comp ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))).mul
        (by fun_prop)))
  have hlog : ((Real.log 2).toNNReal : ℝ) = Real.log 2 :=
    Real.coe_toNNReal _ (Real.log_nonneg one_le_two)
  calc ∫⁻ ω, ∫⁻ z, g z * ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
          rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z))) ∂ν ∂P
      = ∫⁻ z, ∫⁻ ω, g z * ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
          rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z))) ∂P ∂ν :=
        hh.lintegral_lintegral_circle_swap
          (F := fun z p => g z * ENNReal.ofReal (I (p.2.1 - p.2.2) * rexp (γ * (p.1 - p.2.1))))
          (half_pos hε) hε hR ν hF
    _ ≤ ∫⁻ z, g z * (ENNReal.ofReal (rexp (γ ^ 2 * Real.log 2 / 2)) *
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
        have hDm : Measurable fun ω => hcirc ω (ε / 2) z - hcirc ω ε z :=
          (hh.measurable_circle (ε / 2) z (half_pos hε)).sub (hh.measurable_circle ε z hε)
        have hA : Measurable fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)) :=
          ENNReal.measurable_ofReal.comp (hI.comp hXm)
        have hB : Measurable fun ω => ENNReal.ofReal (rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z))) :=
          ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).comp hDm)
        have hind : IndepFun (fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)))
            (fun ω => ENNReal.ofReal (rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z)))) P :=
          (hh.indepFun_recentred_increment hε hz).comp (ENNReal.measurable_ofReal.comp hI)
            (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)))
        have hsplit : ∀ ω, ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
            rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z))) =
            (fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0)) *
              ENNReal.ofReal (rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z)))) ω :=
          fun ω => ENNReal.ofReal_mul (hI0 _)
        have hAB : Measurable fun ω => ENNReal.ofReal (I (hcirc ω ε z - hcirc ω R 0) *
            rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z))) :=
          ENNReal.measurable_ofReal.comp ((hI.comp hXm).mul
            ((by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).comp hDm))
        rw [lintegral_const_mul (g z) hAB]
        gcongr
        rw [lintegral_congr hsplit]
        have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun hA hB hind
        simp only [Pi.mul_apply] at hmul ⊢
        rw [hmul, mul_comm]
        have hexp := GaussTail.lintegral_ofReal_exp_mul_of_hasLaw (hh.hasLaw_increment hε z) γ
        rw [hlog] at hexp
        rw [hexp]
        gcongr
        have h := GaussTail.lintegral_ofReal_indicator_Ici_exp_mul_le_of_hasLaw
          (hh.hasLaw_recentred_circle hε hz) hγα
        rw [hL] at h
        exact h
    _ = _ := lintegral_mul_const _ hg

end LatticeProb.Gauss.IsWholePlaneGFF

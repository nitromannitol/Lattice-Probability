import LatticeProb.LQG.GMCThinPart

/-!
# L¹ rate of the dyadic increments of circle-average Gaussian multiplicative chaos

For a whole-plane Gaussian free field with circle averages `h_r(z)`, recentred at `h_R(0)`, and a weight `g`
supported where `‖z‖ + ε ≤ R`, consider the increment between the normalized exponentials at radii `ε / 2` and `ε`,
`Δ_z = (ε/2)^{γ²/2} e^{γ (h_{ε/2}(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}`.

## Main results

* `IsWholePlaneGFF.lintegral_lintegral_enorm_mul_exp_eq`: `E ∫ |g(z)| e^{γ (h_r(z) - h_R(0))} dν(z)
  = (∫ |g| dν) (R / r)^{γ²/2}` (as lower Lebesgue integrals).
* `IsWholePlaneGFF.integrable_prod_mul_exp_recentred`: for a jointly measurable modification `H` of the circle
  averages, `(ω, z) ↦ g(z) e^{γ (H_r(z) - H_R(0))}` is integrable for the product measure.
* `IsWholePlaneGFF.integrable_integral_increment`: `ω ↦ ∫ g Δ dν` is integrable.
* `IsWholePlaneGFF.integral_abs_integral_increment_le`: for `γ ≤ α ≤ 2γ` and `t > 0`,
  `E |∫ g Δ dν| ≤ ε^{γ²/2} ((B I / t + t) / 2 + 2 (∫ |g| dν) e^{L (γ²/2 - (α - γ)²/2)})`, `L = log (R / ε)`,
  with `B I` the second-moment bound of the thin-point part: the increment splits as
  `Δ_z = ε^{γ²/2} (T_z + K_z)` into the thin points `X_z ≤ α L` (second moment, finite range of dependence) and the
  thick points `X_z > α L` (first moment).
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

namespace LatticeProb.Gauss.IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `E ∫ |g(z)| e^{γ (h_r(z) - h_R(0))} dν(z) = (∫ |g| dν) e^{γ² log (R / r) / 2}` for a measurable weight `g`
supported where `‖z‖ + r ≤ R`. -/
theorem lintegral_lintegral_enorm_mul_exp_eq (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ} (hr : 0 < r)
    (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hg : Measurable g)
    (hgs : ∀ z, g z ≠ 0 → ‖z‖ + r ≤ R) (γ : ℝ) :
    ∫⁻ ω, ∫⁻ z, ‖g z * rexp (γ * (hcirc ω r z - hcirc ω R 0))‖ₑ ∂ν ∂P =
      (∫⁻ z, ‖g z‖ₑ ∂ν) * ENNReal.ofReal (rexp (γ ^ 2 * Real.log (R / r) / 2)) := by
  have hF : Measurable (uncurry fun (z : ℂ) (p : ℝ × ℝ × ℝ) => ‖g z * rexp (γ * (p.1 - p.2.2))‖ₑ) :=
    ((hg.comp measurable_fst).mul (Real.measurable_exp.comp (measurable_const.mul
      ((measurable_fst.comp measurable_snd).sub
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))))).enorm
  calc ∫⁻ ω, ∫⁻ z, ‖g z * rexp (γ * (hcirc ω r z - hcirc ω R 0))‖ₑ ∂ν ∂P
      = ∫⁻ z, ∫⁻ ω, ‖g z * rexp (γ * (hcirc ω r z - hcirc ω R 0))‖ₑ ∂P ∂ν :=
        hh.lintegral_lintegral_circle_swap (F := fun z p => ‖g z * rexp (γ * (p.1 - p.2.2))‖ₑ) hr hr hR ν hF
    _ = ∫⁻ z, ‖g z‖ₑ * ENNReal.ofReal (rexp (γ ^ 2 * Real.log (R / r) / 2)) ∂ν := by
        refine lintegral_congr fun z => ?_
        simp_rw [enorm_mul, Real.enorm_eq_ofReal (Real.exp_pos _).le]
        by_cases hz0 : g z = 0
        · simp [hz0]
        have hz := hgs z hz0
        have hrR : r ≤ R := by linarith [norm_nonneg z]
        have hL : ((Real.log (R / r)).toNNReal : ℝ) = Real.log (R / r) :=
          Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hr).mpr hrR))
        have hXm : Measurable fun ω => hcirc ω r z - hcirc ω R 0 :=
          (hh.measurable_circle r z hr).sub (hh.measurable_circle R 0 hR)
        rw [lintegral_const_mul _ (show Measurable fun ω => ENNReal.ofReal (rexp (γ * (hcirc ω r z - hcirc ω R 0)))
          from ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hXm.const_mul γ)))]
        have h := GaussTail.lintegral_ofReal_exp_mul_of_hasLaw (hh.hasLaw_recentred_circle hr hz) γ
        rw [hL] at h
        rw [h]
    _ = _ := lintegral_mul_const _ hg.enorm

/-- For a jointly measurable modification `H` of the circle averages, the weighted exponential
`(ω, z) ↦ g(z) e^{γ (H_r(z) - H_R(0))}` is integrable for `P ⊗ ν`. -/
theorem integrable_prod_mul_exp_recentred (hh : IsWholePlaneGFF P hC hcirc) {H : Ω → ℝ → ℂ → ℝ}
    (hHm : ∀ r, 0 < r → Measurable (fun p : ℂ × Ω => H p.2 r p.1))
    (hHae : ∀ᵐ ω ∂P, ∀ r z, H ω r z = hcirc ω r z) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (hgs : ∀ z, g z ≠ 0 → ‖z‖ + r ≤ R) (γ : ℝ) :
    Integrable (fun q : Ω × ℂ => g q.2 * rexp (γ * (H q.1 r q.2 - H q.1 R 0))) (P.prod ν) := by
  have := hh.isProbabilityMeasure
  have hm1 : Measurable fun q : Ω × ℂ => H q.1 r q.2 := (hHm r hr).comp measurable_swap
  have hm3 : Measurable fun q : Ω × ℂ => H q.1 R 0 :=
    (hHm R hR).comp (measurable_const.prodMk measurable_fst)
  have hm : Measurable fun q : Ω × ℂ => g q.2 * rexp (γ * (H q.1 r q.2 - H q.1 R 0)) :=
    (hgm.comp measurable_snd).mul (Real.measurable_exp.comp (measurable_const.mul (hm1.sub hm3)))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm.enorm.aemeasurable]
  calc ∫⁻ ω, ∫⁻ z, ‖g (ω, z).2 * rexp (γ * (H (ω, z).1 r (ω, z).2 - H (ω, z).1 R 0))‖ₑ ∂ν ∂P
      = ∫⁻ ω, ∫⁻ z, ‖g z * rexp (γ * (hcirc ω r z - hcirc ω R 0))‖ₑ ∂ν ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hHae] with ω hω
        simp only [hω]
    _ = _ := hh.lintegral_lintegral_enorm_mul_exp_eq hr hR ν hgm hgs γ
    _ < ⊤ := ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.mp hg.2) ENNReal.ofReal_lt_top

/-- The increment `ω ↦ ∫ g(z) ((ε/2)^{γ²/2} e^{γ (h_{ε/2}(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}) dν(z)`
is integrable. -/
theorem integrable_integral_increment (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) (γ : ℝ) :
    Integrable (fun ω => ∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν) P := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hgR2 : ∀ z, g z ≠ 0 → ‖z‖ + ε / 2 ≤ R := fun z hz => by linarith [hgR z hz]
  have h1 := (hh.integrable_prod_mul_exp_recentred hHm hHae (half_pos hε) hR ν hgm hg hgR2 γ).const_mul
    ((ε / 2) ^ (γ ^ 2 / 2))
  have h2 := (hh.integrable_prod_mul_exp_recentred hHm hHae hε hR ν hgm hg hgR γ).const_mul (ε ^ (γ ^ 2 / 2))
  have h3 := (h1.sub h2).integral_prod_left
  refine h3.congr ?_
  filter_upwards [hHae] with ω hω
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply, hω]
  ring

/-- **L¹ rate of the dyadic increment.** For `γ ≤ α ≤ 2γ`, `L = log (R / ε)`, a measurable integrable weight `g`
supported where `‖z‖ + ε ≤ R` and every `t > 0`,
`E |∫ g(z) ((ε/2)^{γ²/2} e^{γ (h_{ε/2}(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}) dν(z)|
  ≤ ε^{γ²/2} ((B I / t + t) / 2 + 2 (∫ |g| dν) e^{L (γ²/2 - (α - γ)²/2)})`,
where `B = (2^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}` and `I = ∫_{‖z - w‖ < 2ε} |g(z)| |g(w)| d(ν ⊗ ν)`. -/
theorem integral_abs_integral_increment_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε)
    (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν| ∂P ≤
      ε ^ (γ ^ 2 / 2) * (((rexp (γ ^ 2 * Real.log 2) - 1) *
          rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
          (∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) / t +
            t) / 2 +
        2 * (∫ z, |g z| ∂ν) * rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2))) := by
  classical
  have := hh.isProbabilityMeasure
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hgR2 : ∀ z, g z ≠ 0 → ‖z‖ + ε / 2 ≤ R := fun z hz => by linarith [hgR z hz]
  set c : ℝ := ε ^ (γ ^ 2 / 2) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hε.le _
  set a : ℝ := α * Real.log (R / ε) with ha
  set W : ℝ → ℝ := GaussIndep.expWeight γ (Real.log 2).toNNReal with hW
  set m : ℝ := rexp (-(γ ^ 2 * Real.log 2) / 2) with hm
  have hlog : ((Real.log 2).toNNReal : ℝ) = Real.log 2 := Real.coe_toNNReal _ (Real.log_nonneg one_le_two)
  have hWd : ∀ d, W d = m * rexp (γ * d) - 1 := fun d => by
    simp only [hW, GaussIndep.expWeight, hlog, hm]
  set FT : ℝ → ℝ := (Set.Iic a).indicator fun x => rexp (γ * x) with hFT
  set FK : ℝ → ℝ := (Set.Ioi a).indicator fun x => rexp (γ * x) with hFK
  set FI : ℝ → ℝ := (Set.Ici a).indicator fun x => rexp (γ * x) with hFI
  have hFTm : Measurable FT := (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  have hFKm : Measurable FK := (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Ioi
  have hFIm : Measurable FI := (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Ici
  have hWm : Measurable W := GaussIndep.measurable_expWeight γ _
  -- the deterministic split of the increment into thin and thick points
  have hsum : ∀ x, FT x + FK x = rexp (γ * x) := fun x => by
    rw [hFT, hFK, ← Set.compl_Iic, Set.indicator_self_add_compl_apply]
  have hsplit : ∀ x d, (ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) - c * rexp (γ * x) =
      c * (FT x * W d) + c * (FK x * W d) := fun x d => by
    rw [Gauss.rpow_mul_exp_add_sub_eq hε γ x d, ← hW, ← hsum x]
    ring
  have hfine : ∀ x d, (ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) = c * rexp (γ * x) * (m * rexp (γ * d)) :=
    fun x d => by
      have h := Gauss.rpow_mul_exp_add_sub_eq hε γ x d
      rw [← hW, hWd] at h
      linarith
  have hWabs : ∀ d, |W d| ≤ m * rexp (γ * d) + 1 := fun d => by
    rw [hWd]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (by positivity), abs_one]
  have hFT0 : ∀ x, 0 ≤ FT x := fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  have hFK0 : ∀ x, 0 ≤ FK x := fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  have hFTle : ∀ x, FT x ≤ rexp (γ * x) := fun x => by linarith [hsum x, hFK0 x]
  have hFKle : ∀ x, FK x ≤ rexp (γ * x) := fun x => by linarith [hsum x, hFT0 x]
  have hFKI : ∀ x, FK x ≤ FI x := fun x =>
    Set.indicator_le_indicator_of_subset Set.Ioi_subset_Ici_self (fun _ => (Real.exp_pos _).le) x
  have hdom : ∀ x d {F : ℝ → ℝ}, (∀ x, 0 ≤ F x) → (∀ x, F x ≤ rexp (γ * x)) →
      |c * (F x * W d)| ≤ (ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) + c * rexp (γ * x) := by
    intro x d F hF0 hFle
    rw [hfine, abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg (hF0 x)]
    have h1 := mul_le_mul (hFle x) (hWabs d) (abs_nonneg _) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left h1 hc0]
  -- jointly measurable versions on `Ω × ℂ`
  have hm1 : Measurable fun q : Ω × ℂ => H q.1 ε q.2 := (hHm ε hε).comp measurable_swap
  have hm2 : Measurable fun q : Ω × ℂ => H q.1 (ε / 2) q.2 := (hHm (ε / 2) (half_pos hε)).comp measurable_swap
  have hm3 : Measurable fun q : Ω × ℂ => H q.1 R 0 := (hHm R hR).comp (measurable_const.prodMk measurable_fst)
  set ΦT : Ω × ℂ → ℝ := fun q => g q.2 * (c * (FT (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 (ε / 2) q.2 - H q.1 ε q.2)))
    with hΦTdef
  set ΦK : Ω × ℂ → ℝ := fun q => g q.2 * (c * (FK (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 (ε / 2) q.2 - H q.1 ε q.2)))
    with hΦKdef
  have hΦTm : Measurable ΦT := (hgm.comp measurable_snd).mul (measurable_const.mul
    ((hFTm.comp (hm1.sub hm3)).mul (hWm.comp (hm2.sub hm1))))
  have hΦKm : Measurable ΦK := (hgm.comp measurable_snd).mul (measurable_const.mul
    ((hFKm.comp (hm1.sub hm3)).mul (hWm.comp (hm2.sub hm1))))
  have hG := ((hh.integrable_prod_mul_exp_recentred hHm hHae (half_pos hε) hR ν hgm.abs hg.abs
    (fun z hz => hgR2 z (fun h => hz (by simp [h]))) γ).const_mul ((ε / 2) ^ (γ ^ 2 / 2))).add
    ((hh.integrable_prod_mul_exp_recentred hHm hHae hε hR ν hgm.abs hg.abs
      (fun z hz => hgR z (fun h => hz (by simp [h]))) γ).const_mul c)
  have hbound : ∀ {F : ℝ → ℝ}, (∀ x, 0 ≤ F x) → (∀ x, F x ≤ rexp (γ * x)) → ∀ q : Ω × ℂ,
      ‖g q.2 * (c * (F (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 (ε / 2) q.2 - H q.1 ε q.2)))‖ ≤
        (ε / 2) ^ (γ ^ 2 / 2) * (|g q.2| * rexp (γ * (H q.1 (ε / 2) q.2 - H q.1 R 0))) +
          c * (|g q.2| * rexp (γ * (H q.1 ε q.2 - H q.1 R 0))) := by
    intro F hF0 hFle q
    have h := hdom (H q.1 ε q.2 - H q.1 R 0) (H q.1 (ε / 2) q.2 - H q.1 ε q.2) hF0 hFle
    have hxd : H q.1 ε q.2 - H q.1 R 0 + (H q.1 (ε / 2) q.2 - H q.1 ε q.2) = H q.1 (ε / 2) q.2 - H q.1 R 0 := by
      ring
    rw [hxd] at h
    rw [Real.norm_eq_abs, abs_mul]
    calc |g q.2| * |c * (F (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 (ε / 2) q.2 - H q.1 ε q.2))|
        ≤ |g q.2| * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (H q.1 (ε / 2) q.2 - H q.1 R 0)) +
          c * rexp (γ * (H q.1 ε q.2 - H q.1 R 0))) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = _ := by ring
  have hΦT : Integrable ΦT (P.prod ν) :=
    hG.mono' hΦTm.aestronglyMeasurable (ae_of_all _ fun q => hbound hFT0 hFTle q)
  have hΦK : Integrable ΦK (P.prod ν) :=
    hG.mono' hΦKm.aestronglyMeasurable (ae_of_all _ fun q => hbound hFK0 hFKle q)
  have hFI0 : ∀ x, 0 ≤ FI x := fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x
  have hm0 : 0 ≤ m := (Real.exp_pos _).le
  have hgI0 : 0 ≤ ∫ z, |g z| ∂ν := integral_nonneg fun _ => abs_nonneg _
  -- sample by sample: `|∫ g Δ| ≤ |∫ g c T| + ∫ |g c K|`
  have hY := hh.integrable_integral_increment hε hR ν hgm hg hgR γ
  have hTint := hΦT.integral_prod_left
  have hKint := hΦK.integral_norm_prod_left
  have hpt : ∀ᵐ ω ∂P, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω R 0)) -
        c * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν| ≤
      |∫ z, ΦT (ω, z) ∂ν| + ∫ z, ‖ΦK (ω, z)‖ ∂ν := by
    filter_upwards [hHae, hΦT.prod_right_ae, hΦK.prod_right_ae] with ω hω hT hK
    have heq : ∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω R 0)) -
        c * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν = ∫ z, ΦT (ω, z) ∂ν + ∫ z, ΦK (ω, z) ∂ν := by
      refine (integral_congr_ae (ae_of_all _ fun z => ?_)).trans (integral_add hT hK)
      have hxd : hcirc ω (ε / 2) z - hcirc ω R 0 =
          (hcirc ω ε z - hcirc ω R 0) + (hcirc ω (ε / 2) z - hcirc ω ε z) := by ring
      simp only [hΦTdef, hΦKdef, hω]
      rw [hxd, hsplit, mul_add]
    rw [heq]
    have h2 := norm_integral_le_integral_norm (μ := ν) (fun z => ΦK (ω, z))
    rw [Real.norm_eq_abs] at h2
    exact (abs_add_le _ _).trans (add_le_add le_rfl h2)
  -- thin points
  have hthin : ∫ ω, |∫ z, ΦT (ω, z) ∂ν| ∂P ≤
      c * (((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
          (∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) / t +
            t) / 2) := by
    have hcongr : (fun ω => |∫ z, ΦT (ω, z) ∂ν|) =ᵐ[P] fun ω =>
        c * |∫ z, g z * (FT (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z)) ∂ν| := by
      filter_upwards [hHae] with ω hω
      have h1 : ∀ z, ΦT (ω, z) =
          c * (g z * (FT (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z))) := fun z => by
        simp only [hΦTdef, hω]
        ring
      simp_rw [h1, integral_const_mul, abs_mul, abs_of_nonneg hc0]
    rw [integral_congr_ae hcongr, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hh.integral_abs_integral_thin_le hε hR ν hgm hg hgR hα ht) hc0
  -- thick points
  have hthick : ∫ ω, ∫ z, ‖ΦK (ω, z)‖ ∂ν ∂P ≤
      c * (2 * (∫ z, |g z| ∂ν) * rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2))) := by
    set eL := rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) with heL
    set e2 := rexp (γ ^ 2 * Real.log 2 / 2) with he2
    have e1 : ∫ ω, ∫ z, ‖ΦK (ω, z)‖ ∂ν ∂P = ∫ q, ‖ΦK q‖ ∂(P.prod ν) := (integral_prod _ hΦK.norm).symm
    rw [e1, integral_norm_eq_lintegral_enorm hΦKm.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc0 (mul_nonneg (mul_nonneg zero_le_two hgI0)
      (Real.exp_pos _).le)) ?_
    have e3 : ∫⁻ q, ‖ΦK q‖ₑ ∂(P.prod ν) = ∫⁻ ω, ∫⁻ z, ‖ΦK (ω, z)‖ₑ ∂ν ∂P :=
      lintegral_prod _ hΦKm.enorm.aemeasurable
    rw [e3]
    set A1 : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (c * m * |g q.2|) *
      ENNReal.ofReal (FI (H q.1 ε q.2 - H q.1 R 0) * rexp (γ * (H q.1 (ε / 2) q.2 - H q.1 ε q.2))) with hA1
    set A2 : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (c * |g q.2|) *
      ENNReal.ofReal (FI (H q.1 ε q.2 - H q.1 R 0)) with hA2
    have hA1m : Measurable A1 :=
      (ENNReal.measurable_ofReal.comp (measurable_const.mul (hgm.comp measurable_snd).abs)).mul
        (ENNReal.measurable_ofReal.comp ((hFIm.comp (hm1.sub hm3)).mul
          (Real.measurable_exp.comp ((hm2.sub hm1).const_mul γ))))
    have hpw : ∀ q, ‖ΦK q‖ₑ ≤ A1 q + A2 q := by
      intro q
      have hX0 := hFI0 (H q.1 ε q.2 - H q.1 R 0)
      have hcmg : 0 ≤ c * m * |g q.2| := mul_nonneg (mul_nonneg hc0 hm0) (abs_nonneg _)
      have hcg : 0 ≤ c * |g q.2| := mul_nonneg hc0 (abs_nonneg _)
      rw [Real.enorm_eq_ofReal_abs, hA1, hA2]
      beta_reduce
      rw [← ENNReal.ofReal_mul hcmg, ← ENNReal.ofReal_mul hcg,
        ← ENNReal.ofReal_add (mul_nonneg hcmg (mul_nonneg hX0 (Real.exp_pos _).le)) (mul_nonneg hcg hX0)]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [hΦKdef]
      rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg (hFK0 _)]
      have h1 := mul_le_mul (hFKI (H q.1 ε q.2 - H q.1 R 0)) (hWabs (H q.1 (ε / 2) q.2 - H q.1 ε q.2))
        (abs_nonneg _) hX0
      calc |g q.2| * (c * (FK (H q.1 ε q.2 - H q.1 R 0) * |W (H q.1 (ε / 2) q.2 - H q.1 ε q.2)|))
          ≤ |g q.2| * (c * (FI (H q.1 ε q.2 - H q.1 R 0) *
              (m * rexp (γ * (H q.1 (ε / 2) q.2 - H q.1 ε q.2)) + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hc0) (abs_nonneg _)
        _ = _ := by ring
    have hgs' : ∀ k : ℝ, ∀ z, ENNReal.ofReal (k * |g z|) ≠ 0 → ‖z‖ + ε ≤ R := fun k z hz =>
      hgR z (fun h => hz (by simp [h]))
    calc ∫⁻ ω, ∫⁻ z, ‖ΦK (ω, z)‖ₑ ∂ν ∂P ≤ ∫⁻ ω, ∫⁻ z, (A1 (ω, z) + A2 (ω, z)) ∂ν ∂P :=
          lintegral_mono fun ω => lintegral_mono fun z => hpw (ω, z)
      _ = ∫⁻ ω, ∫⁻ z, A1 (ω, z) ∂ν ∂P + ∫⁻ ω, ∫⁻ z, A2 (ω, z) ∂ν ∂P := by
          rw [← lintegral_add_left hA1m.lintegral_prod_right']
          exact lintegral_congr fun ω => lintegral_add_left (hA1m.comp measurable_prodMk_left) _
      _ ≤ (∫⁻ z, ENNReal.ofReal (c * m * |g z|) ∂ν) * (ENNReal.ofReal e2 * ENNReal.ofReal eL) +
            (∫⁻ z, ENNReal.ofReal (c * |g z|) ∂ν) * ENNReal.ofReal eL := by
          refine add_le_add ?_ ?_
          · have e : ∫⁻ ω, ∫⁻ z, A1 (ω, z) ∂ν ∂P = ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (c * m * |g z|) *
                ENNReal.ofReal (FI (hcirc ω ε z - hcirc ω R 0) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω ε z)))
                  ∂ν ∂P := by
              refine lintegral_congr_ae ?_
              filter_upwards [hHae] with ω hω
              simp only [hA1, hω]
            rw [e]
            exact hh.lintegral_lintegral_thick_mul_exp_increment_le hε hR hγα ν
              (ENNReal.measurable_ofReal.comp (measurable_const.mul hgm.abs)) (hgs' (c * m))
          · have e : ∫⁻ ω, ∫⁻ z, A2 (ω, z) ∂ν ∂P = ∫⁻ ω, ∫⁻ z, ENNReal.ofReal (c * |g z|) *
                ENNReal.ofReal (FI (hcirc ω ε z - hcirc ω R 0)) ∂ν ∂P := by
              refine lintegral_congr_ae ?_
              filter_upwards [hHae] with ω hω
              simp only [hA2, hω]
            rw [e]
            exact hh.lintegral_lintegral_thick_le hε hR hγα ν
              (ENNReal.measurable_ofReal.comp (measurable_const.mul hgm.abs)) (hgs' c)
      _ = ENNReal.ofReal (c * (2 * (∫ z, |g z| ∂ν) * eL)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hg.abs.const_mul (c * m))
              (ae_of_all _ fun z => mul_nonneg (mul_nonneg hc0 hm0) (abs_nonneg _)),
            ← ofReal_integral_eq_lintegral_ofReal (hg.abs.const_mul c)
              (ae_of_all _ fun z => mul_nonneg hc0 (abs_nonneg _)),
            integral_const_mul, integral_const_mul,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hc0 hm0) hgI0),
            ← ENNReal.ofReal_mul (mul_nonneg hc0 hgI0),
            ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (mul_nonneg hc0 hm0) hgI0)
              (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (mul_nonneg (mul_nonneg hc0 hgI0)
                (Real.exp_pos _).le)]
          congr 1
          have hme : m * e2 = 1 := by
            rw [hm, he2, ← Real.exp_add, ← Real.exp_zero]
            congr 1
            ring
          linear_combination (c * (∫ z, |g z| ∂ν) * eL) * hme
  calc ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω R 0)) -
        c * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν| ∂P
      ≤ ∫ ω, (|∫ z, ΦT (ω, z) ∂ν| + ∫ z, ‖ΦK (ω, z)‖ ∂ν) ∂P :=
        integral_mono_ae hY.abs (hTint.abs.add hKint) hpt
    _ = ∫ ω, |∫ z, ΦT (ω, z) ∂ν| ∂P + ∫ ω, ∫ z, ‖ΦK (ω, z)‖ ∂ν ∂P := integral_add hTint.abs hKint
    _ ≤ _ := add_le_add hthin hthick
    _ = _ := by ring

end LatticeProb.Gauss.IsWholePlaneGFF

import LatticeProb.LQG.GMCL1Rate
import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.LQG.GMCPointwiseMomentsLe
import LatticeProb.LQG.GMCThickPartLe
import LatticeProb.LQG.GMCThinPartLe
import LatticeProb.LQG.LQGCoordChangeIdent

/-!
# L¹ rate of the increments of circle-average Gaussian multiplicative chaos between scales of ratio at most `2`

For a whole-plane Gaussian free field with circle averages `h_r(z)`, recentred at `h_R(0)`, and a weight `g`
supported where `‖z‖ + ε ≤ R`, consider for `0 < s ≤ ε` the increment between the normalized exponentials at
radii `s` and `ε`,
`Δ_z = s^{γ²/2} e^{γ (h_s(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}`.
This is the version of the dyadic increment bound (`s = ε / 2`) with a free ratio `ε / s`.

## Main results

* `IsWholePlaneGFF.integral_abs_integral_increment_le_of_le`: for `γ ≤ α ≤ 2γ` and `t > 0`,
  `E |∫ g Δ dν| ≤ ε^{γ²/2} ((B I / t + t) / 2 + 2 (∫ |g| dν) e^{L (γ²/2 - (α - γ)²/2)})`, `L = log (R / ε)`,
  `B = ((ε/s)^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}`.
* `IsWholePlaneGFF.integral_abs_integral_increment_le_exp_of_le`: for a bounded weight and `ε / 2 ≤ s ≤ ε`, the
  same bound in exponential form `K₁ ε^{b/2} + K₂ ε^{(α-γ)²/2}` with constants independent of `s` and `ε`.
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

namespace LatticeProb.Gauss.IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **L¹ rate of the increment at a general scale ratio.** For `0 < s ≤ ε`, `γ ≤ α ≤ 2γ`, `L = log (R / ε)`, a
measurable integrable weight `g` supported where `‖z‖ + ε ≤ R` and every `t > 0`,
`E |∫ g(z) (s^{γ²/2} e^{γ (h_s(z) - h_R(0))} - ε^{γ²/2} e^{γ (h_ε(z) - h_R(0))}) dν(z)|
  ≤ ε^{γ²/2} ((B I / t + t) / 2 + 2 (∫ |g| dν) e^{L (γ²/2 - (α - γ)²/2)})`,
where `B = ((ε/s)^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}` and `I = ∫_{‖z - w‖ < 2ε} |g(z)| |g(w)| d(ν ⊗ ν)`. -/
theorem integral_abs_integral_increment_le_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g)
    (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν| ∂P ≤
      ε ^ (γ ^ 2 / 2) * (((rexp (γ ^ 2 * Real.log (ε / s)) - 1) *
          rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
          (∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) / t +
            t) / 2 +
        2 * (∫ z, |g z| ∂ν) * rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2))) := by
  classical
  have := hh.isProbabilityMeasure
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ + s ≤ R := fun z hz => by linarith [hgR z hz, hsε]
  set c : ℝ := ε ^ (γ ^ 2 / 2) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hε.le _
  set a : ℝ := α * Real.log (R / ε) with ha
  set W : ℝ → ℝ := GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal with hW
  set m : ℝ := rexp (-(γ ^ 2 * Real.log (ε / s)) / 2) with hm
  have hlog : ((Real.log (ε / s)).toNNReal : ℝ) = Real.log (ε / s) := Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hs).mpr hsε))
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
  have hsplit : ∀ x d, s ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) - c * rexp (γ * x) =
      c * (FT x * W d) + c * (FK x * W d) := fun x d => by
    rw [GaussTail.rpow_mul_exp_add_sub_eq_of_le hs hsε γ x d, ← hW, ← hsum x]
    ring
  have hfine : ∀ x d, s ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) = c * rexp (γ * x) * (m * rexp (γ * d)) :=
    fun x d => by
      have h := GaussTail.rpow_mul_exp_add_sub_eq_of_le hs hsε γ x d
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
      |c * (F x * W d)| ≤ s ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) + c * rexp (γ * x) := by
    intro x d F hF0 hFle
    rw [hfine, abs_mul, abs_of_nonneg hc0, abs_mul, abs_of_nonneg (hF0 x)]
    have h1 := mul_le_mul (hFle x) (hWabs d) (abs_nonneg _) (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left h1 hc0]
  -- jointly measurable versions on `Ω × ℂ`
  have hm1 : Measurable fun q : Ω × ℂ => H q.1 ε q.2 := (hHm ε hε).comp measurable_swap
  have hm2 : Measurable fun q : Ω × ℂ => H q.1 s q.2 := (hHm s hs).comp measurable_swap
  have hm3 : Measurable fun q : Ω × ℂ => H q.1 R 0 := (hHm R hR).comp (measurable_const.prodMk measurable_fst)
  set ΦT : Ω × ℂ → ℝ := fun q => g q.2 * (c * (FT (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 s q.2 - H q.1 ε q.2)))
    with hΦTdef
  set ΦK : Ω × ℂ → ℝ := fun q => g q.2 * (c * (FK (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 s q.2 - H q.1 ε q.2)))
    with hΦKdef
  have hΦTm : Measurable ΦT := (hgm.comp measurable_snd).mul (measurable_const.mul
    ((hFTm.comp (hm1.sub hm3)).mul (hWm.comp (hm2.sub hm1))))
  have hΦKm : Measurable ΦK := (hgm.comp measurable_snd).mul (measurable_const.mul
    ((hFKm.comp (hm1.sub hm3)).mul (hWm.comp (hm2.sub hm1))))
  have hG := ((hh.integrable_prod_mul_exp_recentred hHm hHae hs hR ν hgm.abs hg.abs
    (fun z hz => hgs z (fun h => hz (by simp [h]))) γ).const_mul (s ^ (γ ^ 2 / 2))).add
    ((hh.integrable_prod_mul_exp_recentred hHm hHae hε hR ν hgm.abs hg.abs
      (fun z hz => hgR z (fun h => hz (by simp [h]))) γ).const_mul c)
  have hbound : ∀ {F : ℝ → ℝ}, (∀ x, 0 ≤ F x) → (∀ x, F x ≤ rexp (γ * x)) → ∀ q : Ω × ℂ,
      ‖g q.2 * (c * (F (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 s q.2 - H q.1 ε q.2)))‖ ≤
        s ^ (γ ^ 2 / 2) * (|g q.2| * rexp (γ * (H q.1 s q.2 - H q.1 R 0))) +
          c * (|g q.2| * rexp (γ * (H q.1 ε q.2 - H q.1 R 0))) := by
    intro F hF0 hFle q
    have h := hdom (H q.1 ε q.2 - H q.1 R 0) (H q.1 s q.2 - H q.1 ε q.2) hF0 hFle
    have hxd : H q.1 ε q.2 - H q.1 R 0 + (H q.1 s q.2 - H q.1 ε q.2) = H q.1 s q.2 - H q.1 R 0 := by
      ring
    rw [hxd] at h
    rw [Real.norm_eq_abs, abs_mul]
    calc |g q.2| * |c * (F (H q.1 ε q.2 - H q.1 R 0) * W (H q.1 s q.2 - H q.1 ε q.2))|
        ≤ |g q.2| * (s ^ (γ ^ 2 / 2) * rexp (γ * (H q.1 s q.2 - H q.1 R 0)) +
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
  have hY := hh.integrable_integral_increment_scales hs hε hR ν hgm hg hgs hgR γ
  have hTint := hΦT.integral_prod_left
  have hKint := hΦK.integral_norm_prod_left
  have hpt : ∀ᵐ ω ∂P, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        c * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν| ≤
      |∫ z, ΦT (ω, z) ∂ν| + ∫ z, ‖ΦK (ω, z)‖ ∂ν := by
    filter_upwards [hHae, hΦT.prod_right_ae, hΦK.prod_right_ae] with ω hω hT hK
    have heq : ∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        c * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν = ∫ z, ΦT (ω, z) ∂ν + ∫ z, ΦK (ω, z) ∂ν := by
      refine (integral_congr_ae (ae_of_all _ fun z => ?_)).trans (integral_add hT hK)
      have hxd : hcirc ω s z - hcirc ω R 0 =
          (hcirc ω ε z - hcirc ω R 0) + (hcirc ω s z - hcirc ω ε z) := by ring
      simp only [hΦTdef, hΦKdef, hω]
      rw [hxd, hsplit, mul_add]
    rw [heq]
    have h2 := norm_integral_le_integral_norm (μ := ν) (fun z => ΦK (ω, z))
    rw [Real.norm_eq_abs] at h2
    exact (abs_add_le _ _).trans (add_le_add le_rfl h2)
  -- thin points
  have hthin : ∫ ω, |∫ z, ΦT (ω, z) ∂ν| ∂P ≤
      c * (((rexp (γ ^ 2 * Real.log (ε / s)) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
          (∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) / t +
            t) / 2) := by
    have hcongr : (fun ω => |∫ z, ΦT (ω, z) ∂ν|) =ᵐ[P] fun ω =>
        c * |∫ z, g z * (FT (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω s z - hcirc ω ε z)) ∂ν| := by
      filter_upwards [hHae] with ω hω
      have h1 : ∀ z, ΦT (ω, z) =
          c * (g z * (FT (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω s z - hcirc ω ε z))) := fun z => by
        simp only [hΦTdef, hω]
        ring
      simp_rw [h1, integral_const_mul, abs_mul, abs_of_nonneg hc0]
    rw [integral_congr_ae hcongr, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hh.integral_abs_integral_thin_le_of_le hs hsε hR ν hgm hg hgR hα ht) hc0
  -- thick points
  have hthick : ∫ ω, ∫ z, ‖ΦK (ω, z)‖ ∂ν ∂P ≤
      c * (2 * (∫ z, |g z| ∂ν) * rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2))) := by
    set eL := rexp (Real.log (R / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) with heL
    set e2 := rexp (γ ^ 2 * Real.log (ε / s) / 2) with he2
    have e1 : ∫ ω, ∫ z, ‖ΦK (ω, z)‖ ∂ν ∂P = ∫ q, ‖ΦK q‖ ∂(P.prod ν) := (integral_prod _ hΦK.norm).symm
    rw [e1, integral_norm_eq_lintegral_enorm hΦKm.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc0 (mul_nonneg (mul_nonneg zero_le_two hgI0)
      (Real.exp_pos _).le)) ?_
    have e3 : ∫⁻ q, ‖ΦK q‖ₑ ∂(P.prod ν) = ∫⁻ ω, ∫⁻ z, ‖ΦK (ω, z)‖ₑ ∂ν ∂P :=
      lintegral_prod _ hΦKm.enorm.aemeasurable
    rw [e3]
    set A1 : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (c * m * |g q.2|) *
      ENNReal.ofReal (FI (H q.1 ε q.2 - H q.1 R 0) * rexp (γ * (H q.1 s q.2 - H q.1 ε q.2))) with hA1
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
      have h1 := mul_le_mul (hFKI (H q.1 ε q.2 - H q.1 R 0)) (hWabs (H q.1 s q.2 - H q.1 ε q.2))
        (abs_nonneg _) hX0
      calc |g q.2| * (c * (FK (H q.1 ε q.2 - H q.1 R 0) * |W (H q.1 s q.2 - H q.1 ε q.2)|))
          ≤ |g q.2| * (c * (FI (H q.1 ε q.2 - H q.1 R 0) *
              (m * rexp (γ * (H q.1 s q.2 - H q.1 ε q.2)) + 1))) :=
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
                ENNReal.ofReal (FI (hcirc ω ε z - hcirc ω R 0) * rexp (γ * (hcirc ω s z - hcirc ω ε z)))
                  ∂ν ∂P := by
              refine lintegral_congr_ae ?_
              filter_upwards [hHae] with ω hω
              simp only [hA1, hω]
            rw [e]
            exact hh.lintegral_lintegral_thick_mul_exp_incr_le hs hsε hR hγα ν
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
  calc ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        c * rexp (γ * (hcirc ω ε z - hcirc ω R 0))) ∂ν| ∂P
      ≤ ∫ ω, (|∫ z, ΦT (ω, z) ∂ν| + ∫ z, ‖ΦK (ω, z)‖ ∂ν) ∂P :=
        integral_mono_ae hY.abs (hTint.abs.add hKint) hpt
    _ = ∫ ω, |∫ z, ΦT (ω, z) ∂ν| ∂P + ∫ ω, ∫ z, ‖ΦK (ω, z)‖ ∂ν ∂P := integral_add hTint.abs hKint
    _ ≤ _ := add_le_add hthin hthick
    _ = _ := by ring

/-- **L¹ rate at a general scale ratio in exponential form.** For `|g| ≤ C`, `ε / 2 ≤ s ≤ ε`, `γ ≤ α ≤ 2γ`,
`p = 2γ² - (2γ - α)²/2`, `b = 2 - γ² + (2γ - α)²/2` and `A = ∫ |g|`,
`E |∫ g Δ| ≤ ((2^{γ²} - 1) R^p · 4π C A + 1)/2 · ε^{b/2} + 2 A R^{γ²/2 - (α-γ)²/2} ε^{(α - γ)²/2}`,
where `Δ` is the increment between the recentred normalized exponentials at radii `s` and `ε`. -/
theorem integral_abs_integral_increment_le_exp_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) (hs2 : ε / 2 ≤ s) (hR : 0 < R) {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g) {C : ℝ}
    (hC : ∀ z, |g z| ≤ C) (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ) :
    ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤
      ((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log R * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
          (C * π * 4 * ∫ z, |g z|) + 1) / 2 * rexp (Real.log ε * ((2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2)) +
        2 * (∫ z, |g z|) * rexp (Real.log R * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) *
          rexp (Real.log ε * ((α - γ) ^ 2 / 2)) := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hM := hh.integral_abs_integral_increment_le_of_le hs hsε hR volume hgm hg hgR hγα hα
    (t := rexp (Real.log ε * ((2 - (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) / 2))) (Real.exp_pos _)
  have hI := Gauss.integral_indicator_norm_sub_lt_le hg hC (2 * ε)
  have hball : volume.real (Metric.ball (0 : ℂ) (2 * ε)) = π * (4 * rexp (Real.log ε * 2)) := by
    rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal, NNReal.coe_real_pi, ← Real.rpow_def_of_pos hε,
      Real.rpow_two]
    ring
  rw [hball] at hI
  have hL : Real.log (R / ε) = Real.log R - Real.log ε := Real.log_div hR.ne' hε.ne'
  have hεu : ε ^ (γ ^ 2 / 2) = rexp (Real.log ε * (γ ^ 2 / 2)) := Real.rpow_def_of_pos hε _
  -- the ratio `ε / s ≤ 2`
  have hratio : ε / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
  have hB1 : 0 ≤ rexp (γ ^ 2 * Real.log (ε / s)) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (mul_nonneg (sq_nonneg γ) (Real.log_nonneg ((one_le_div hs).mpr hsε))))
  have hBle : rexp (γ ^ 2 * Real.log (ε / s)) - 1 ≤ rexp (γ ^ 2 * Real.log 2) - 1 := by
    have := Real.log_le_log (div_pos hε hs) hratio
    have := mul_le_mul_of_nonneg_left this (sq_nonneg γ)
    linarith [Real.exp_le_exp.mpr this]
  have hB0 : 0 ≤ rexp (γ ^ 2 * Real.log 2) - 1 := hB1.trans hBle
  have hI0 : 0 ≤ ∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(volume.prod volume) :=
    integral_nonneg fun p => Set.indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) p
  refine hM.trans ?_
  rw [hL, hεu]
  set u := Real.log ε with hu
  set v := Real.log R with hv
  set A := ∫ z, |g z| with hA
  set B0 := rexp (γ ^ 2 * Real.log 2) - 1 with hB0def
  set B1 := rexp (γ ^ 2 * Real.log (ε / s)) - 1 with hB1def
  set p := 2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2 with hp
  set q := γ ^ 2 / 2 - (α - γ) ^ 2 / 2 with hq
  set e0 := (2 - p) / 2 with he0
  set bb := (2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 with hbb
  calc _ ≤ rexp (u * (γ ^ 2 / 2)) * ((B0 * rexp ((v - u) * p) * (C * (π * (4 * rexp (u * 2))) * A) /
          rexp (u * e0) + rexp (u * e0)) / 2 + 2 * A * rexp ((v - u) * q)) := by
        gcongr
    _ = _ := by
        have k1 : rexp (u * (γ ^ 2 / 2)) * rexp ((v - u) * p) * rexp (u * 2) * rexp (-(u * e0)) =
            rexp (v * p) * rexp (u * bb) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hbb, he0, hp]
          ring
        have k2 : rexp (u * (γ ^ 2 / 2)) * rexp (u * e0) = rexp (u * bb) := by
          rw [← Real.exp_add]
          congr 1
          rw [hbb, he0, hp]
          ring
        have k3 : rexp (u * (γ ^ 2 / 2)) * rexp ((v - u) * q) = rexp (v * q) * rexp (u * ((α - γ) ^ 2 / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          rw [hq]
          ring
        rw [div_eq_mul_inv _ (rexp (u * e0)), ← Real.exp_neg]
        linear_combination (B0 * C * π * 4 * A / 2) * k1 + (1 / 2) * k2 + (2 * A) * k3

end LatticeProb.Gauss.IsWholePlaneGFF

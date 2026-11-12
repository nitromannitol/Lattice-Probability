import LatticeProb.Prob.FiniteRangeSecondMoment
import LatticeProb.LQG.GMCThickPart

/-!
# Thin points of the circle-average approximations of Gaussian multiplicative chaos

Let `h` be a whole-plane GFF with circle averages `h_r(z)`, and write `X_z = h_ε(z) - h_R(0)`,
`D_z = h_{ε/2}(z) - h_ε(z)`, `L = log (R / ε)` and
`T_z = e^{γ X_z} 1{X_z ≤ α L} W(D_z)` with the exponential weight `W(d) = 2^{-γ²/2} e^{γ d} - 1` of variance `log 2`.
Then `ε^{γ²/2} T_z` is the thin-point part of the coarse-to-fine increment
`(ε/2)^{γ²/2} e^{γ (X_z + D_z)} - ε^{γ²/2} e^{γ X_z}` (`LatticeProb.Gauss.rpow_mul_exp_add_sub_eq`).

This file integrates the pointwise thin-point bounds of `LatticeProb.LQG.GMCPointwiseMoments` against a weight `g`
(the second half of the truncated second-moment method of Duplantier-Sheffield 2011, Section 3):
* `integral_sq_integral_thin_le`: for `α ≤ 2γ` and `g` supported where `‖z‖ + ε ≤ R`,
  `E[(∫ g T dν)²] ≤ (2^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)} ∫∫_{‖z - w‖ < 2ε} |g(z)| |g(w)| dν(z) dν(w)`;
  only pairs at distance less than `2ε` contribute, since `T_z` and `T_w` are orthogonal otherwise.
* `integral_abs_integral_thin_le`: the resulting L¹ bound `E|∫ g T dν| ≤ (B I / t + t) / 2`, `t > 0`;
* `integral_indicator_norm_sub_lt_le`: `∫∫_{‖z - w‖ < r} |g(z)| |g(w)| dz dw ≤ C π r² ∫ |g|` for `|g| ≤ C` (Lebesgue).
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

namespace LatticeProb.GaussIndep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {β : Type*} [MeasurableSpace β] {Y : Ω → β}
  {D : Ω → ℝ} {v : ℝ≥0}

/-- The square of the exponential weight is integrable under every Gaussian law. -/
theorem integrable_expWeight_sq (γ : ℝ) (v : ℝ≥0) (m : ℝ) (w : ℝ≥0) :
    Integrable (fun x => expWeight γ v x ^ 2) (gaussianReal m w) := by
  set c := rexp (-(γ ^ 2 * v) / 2)
  have h := (((integrable_exp_mul_gaussianReal (μ := m) (v := w) (2 * γ)).const_mul (c ^ 2)).sub
    ((integrable_exp_mul_gaussianReal (μ := m) (v := w) γ).const_mul (2 * c))).add
    (integrable_const (1 : ℝ))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, expWeight]
  rw [show 2 * γ * x = γ * x + γ * x by ring, Real.exp_add]
  ring

/-- `F(Y) W(D)` is square integrable when `F(Y)` is, for `Y` independent of `D ~ N(0, v)`. -/
theorem integrable_mul_expWeight_sq (hD : HasLaw D (gaussianReal 0 v) P) (hind : IndepFun Y D P) {F : β → ℝ}
    (hF : Measurable F) (hF2 : Integrable (fun ω => F (Y ω) ^ 2) P) (γ : ℝ) :
    Integrable (fun ω => (F (Y ω) * expWeight γ v (D ω)) ^ 2) P := by
  have hW2 : Measurable fun x => expWeight γ v x ^ 2 := (measurable_expWeight γ v).pow_const 2
  have hi : IndepFun ((fun y => F y ^ 2) ∘ Y) ((fun x => expWeight γ v x ^ 2) ∘ D) P :=
    hind.comp (hF.pow_const 2) hW2
  have h := hi.integrable_mul hF2 (hD.integrable_comp (integrable_expWeight_sq γ v 0 v))
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply, Function.comp_apply]
  ring

end LatticeProb.GaussIndep

namespace LatticeProb.Gauss.IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Thin points: `T_z = e^{γ X_z} 1{X_z ≤ a} W(D_z)` is square integrable. -/
theorem integrable_thin_sq (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ‖z‖ + ε ≤ R) (γ a : ℝ) :
    Integrable (fun ω => ((Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z)) ^ 2) P := by
  have hm : Measurable ((Set.Iic a).indicator fun x => rexp (γ * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  refine GaussIndep.integrable_mul_expWeight_sq (hh.hasLaw_increment hε z)
    (hh.indepFun_recentred_increment hε hz) hm ?_ γ
  have hI := (integrable_exp_mul_gaussianReal (μ := 0)
    (v := (Real.log (R / ε)).toNNReal) (2 * γ)).indicator (measurableSet_Iic (a := a))
  refine ((hh.hasLaw_recentred_circle hε hz).integrable_comp hI).congr (ae_of_all _ fun ω => ?_)
  exact (GaussTail.indicator_exp_mul_sq _ γ _).symm

/-- The thin-point integrand `T_z = e^{γ X_z} 1{X_z ≤ α L} W(D_z)` has a modification `T'` jointly measurable in
`(ω, z)`, and `T'_z` inherits the pointwise bounds: square integrability, `E[T'_z²] ≤ (2^{γ²} - 1) e^{L (2γ² - (2γ-α)²/2)}`
and `E[T'_z T'_w] = 0` for `2ε ≤ |z - w|`. -/
theorem exists_measurable_thin (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    {γ α : ℝ} (hα : α ≤ 2 * γ) :
    ∃ TH : Ω → ℂ → ℝ, (Measurable fun q : Ω × ℂ => TH q.1 q.2) ∧
      (∀ᵐ ω ∂P, ∀ z, (Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z) = TH ω z) ∧
      (∀ z, ‖z‖ + ε ≤ R → Integrable (fun ω => TH ω z ^ 2) P) ∧
      (∀ z, ‖z‖ + ε ≤ R → ∫ ω, TH ω z ^ 2 ∂P ≤
        (rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2))) ∧
      (∀ z w, ‖z‖ + ε ≤ R → ‖w‖ + ε ≤ R → 2 * ε ≤ ‖z - w‖ → ∫ ω, TH ω z * TH ω w ∂P = 0) := by
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  set a := α * Real.log (R / ε) with ha
  set F : ℝ → ℝ := (Set.Iic a).indicator fun x => rexp (γ * x) with hFdef
  set W : ℝ → ℝ := GaussIndep.expWeight γ (Real.log 2).toNNReal with hWdef
  have hF : Measurable F :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  have hW : Measurable W := GaussIndep.measurable_expWeight γ _
  set TH : Ω → ℂ → ℝ := fun ω z => F (H ω ε z - H ω R 0) * W (H ω (ε / 2) z - H ω ε z) with hTH
  have hae : ∀ᵐ ω ∂P, ∀ z, F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z) = TH ω z := by
    filter_upwards [hHae] with ω hω z
    simp only [hTH, hω]
  have hTae : ∀ z, (fun ω => F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z)) =ᵐ[P]
      fun ω => TH ω z := fun z => hae.mono fun ω hω => hω z
  have hsq2 : ∀ z, (fun ω => (F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z)) ^ 2) =ᵐ[P]
      fun ω => TH ω z ^ 2 := fun z => hae.mono fun ω hω => by simp only [hω z]
  refine ⟨TH, ?_, hae, fun z hz => (hh.integrable_thin_sq hε hz γ a).congr (hsq2 z), fun z hz => ?_,
    fun z w hz hw hzw => ?_⟩
  · have hm1 : Measurable fun q : Ω × ℂ => H q.1 ε q.2 := (hHm ε hε).comp measurable_swap
    have hm2 : Measurable fun q : Ω × ℂ => H q.1 (ε / 2) q.2 := (hHm (ε / 2) (by positivity)).comp measurable_swap
    have hm3 : Measurable fun q : Ω × ℂ => H q.1 R 0 :=
      (hHm R hR).comp (measurable_const.prodMk measurable_fst)
    exact (hF.comp (hm1.sub hm3)).mul (hW.comp (hm2.sub hm1))
  · rw [← integral_congr_ae (hsq2 z)]
    exact hh.integral_thin_sq_le hε hz hα
  · have hprod : (fun ω => F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z) *
        (F (hcirc ω ε w - hcirc ω R 0) * W (hcirc ω (ε / 2) w - hcirc ω ε w))) =ᵐ[P]
        fun ω => TH ω z * TH ω w := by
      filter_upwards [hTae z, hTae w] with ω h1 h2
      rw [h1, h2]
    rw [← integral_congr_ae hprod]
    exact hh.integral_thin_mul_thin_eq_zero hε hz hw hzw γ a

/-- **Thin points, integrated over the plane.** For `α ≤ 2γ`, `L = log (R / ε)` and an integrable weight `g`
supported where `‖z‖ + ε ≤ R`,
`E[(∫ g(z) e^{γ X_z} 1{X_z ≤ α L} W(D_z) dν(z))²]
  ≤ (2^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)} ∫_{‖z - w‖ < 2ε} |g(z)| |g(w)| d(ν ⊗ ν)(z, w)`. -/
theorem integral_sq_integral_thin_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) :
    ∫ ω, (∫ z, g z * ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z)) ∂ν) ^ 2 ∂P ≤
      (rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
        ∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν) := by
  have := hh.isProbabilityMeasure
  obtain ⟨TH, hTm, hae, hT2, hTB, hTo⟩ := hh.exists_measurable_thin hε hR hα
  have hS : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε} :=
    measurableSet_lt (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable measurable_const
  refine (le_of_eq (integral_congr_ae ?_)).trans (FiniteRange.integral_sq_integral_le hTm hgm hg hS
    (fun z hz => hT2 z (hgR z hz)) (fun z hz => hTB z (hgR z hz))
    (fun z w hz hw hzw => hTo z w (hgR z hz) (hgR w hw) (by simpa [not_lt] using hzw)))
  filter_upwards [hae] with ω hω
  simp only [hω]

/-- The square of the integrated thin part is integrable. -/
theorem integrable_sq_integral_thin (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) :
    Integrable (fun ω => (∫ z, g z * ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z)) ∂ν) ^ 2) P := by
  have := hh.isProbabilityMeasure
  obtain ⟨TH, hTm, hae, hT2, hTB, -⟩ := hh.exists_measurable_thin hε hR hα
  refine (FiniteRange.integrable_sq_integral hTm hgm hg (fun z hz => hT2 z (hgR z hz))
    (fun z hz => hTB z (hgR z hz))).congr ?_
  filter_upwards [hae] with ω hω
  simp only [hω]

/-- **Thin points, L¹ bound.** With `B` the second-moment bound of `integral_sq_integral_thin_le` and
`I = ∫_{‖z - w‖ < 2ε} |g(z)| |g(w)|`, `E|∫ g T dν| ≤ (B I / t + t) / 2` for every `t > 0`. -/
theorem integral_abs_integral_thin_le (hh : IsWholePlaneGFF P hC hcirc) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, |∫ z, g z * ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log 2).toNNReal (hcirc ω (ε / 2) z - hcirc ω ε z)) ∂ν| ∂P ≤
      ((rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
        (∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) / t +
          t) / 2 := by
  have := hh.isProbabilityMeasure
  refine (FiniteRange.integral_abs_le_of_integrable_sq
    (hh.integrable_sq_integral_thin hε hR ν hgm hg hgR hα) ht).trans ?_
  gcongr
  exact hh.integral_sq_integral_thin_le hε hR ν hgm hg hgR hα

end LatticeProb.Gauss.IsWholePlaneGFF

namespace LatticeProb.Gauss

/-- **Area of the near-diagonal.** For an integrable `g : ℂ → ℝ` with `|g| ≤ C`,
`∫_{‖z - w‖ < r} |g(z)| |g(w)| dz dw ≤ C |B_r| ∫ |g|`, where `|B_r| = π r²` is the area of a disk of radius `r`
(`Complex.volume_ball`). -/
theorem integral_indicator_norm_sub_lt_le {g : ℂ → ℝ} (hg : Integrable g) {C : ℝ} (hC : ∀ z, |g z| ≤ C)
    (r : ℝ) :
    ∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < r}.indicator (fun p => |g p.1| * |g p.2|) p ∂(volume.prod volume) ≤
      C * volume.real (Metric.ball (0 : ℂ) r) * ∫ z, |g z| := by
  set S := {p : ℂ × ℂ | ‖p.1 - p.2‖ < r} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable measurable_const
  have hint : Integrable (S.indicator fun p : ℂ × ℂ => |g p.1| * |g p.2|) (volume.prod volume) :=
    (hg.abs.mul_prod hg.abs).indicator hS
  have hsec : ∀ z, (fun w => S.indicator (fun p : ℂ × ℂ => |g p.1| * |g p.2|) (z, w)) =
      fun w => |g z| * (Metric.ball z r).indicator (fun w => |g w|) w := by
    intro z
    funext w
    by_cases hw : ‖z - w‖ < r
    · have h1 : (z, w) ∈ S := hw
      have h2 : w ∈ Metric.ball z r := by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hw
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    · have h1 : (z, w) ∉ S := hw
      have h2 : w ∉ Metric.ball z r := by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hw
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, mul_zero]
  have hball : ∀ z : ℂ, volume.real (Metric.ball z r) = volume.real (Metric.ball (0 : ℂ) r) := by
    intro z
    simp only [measureReal_def, Complex.volume_ball]
  have hin : ∀ z, ∫ w, (Metric.ball z r).indicator (fun w => |g w|) w ≤
      C * volume.real (Metric.ball (0 : ℂ) r) := by
    intro z
    have hfin : volume (Metric.ball z r) ≠ ⊤ := measure_ball_lt_top.ne
    calc ∫ w, (Metric.ball z r).indicator (fun w => |g w|) w
        ≤ ∫ w, (Metric.ball z r).indicator (fun _ => C) w := by
          refine integral_mono (hg.abs.indicator measurableSet_ball)
            ((integrableOn_const hfin).integrable_indicator measurableSet_ball) fun w => ?_
          by_cases hw : w ∈ Metric.ball z r
          · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw]
            exact hC w
          · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw]
      _ = C * volume.real (Metric.ball (0 : ℂ) r) := by
          rw [integral_indicator_const C measurableSet_ball, hball z, smul_eq_mul, mul_comm]
  rw [integral_prod _ hint]
  calc ∫ z, ∫ w, S.indicator (fun p : ℂ × ℂ => |g p.1| * |g p.2|) (z, w)
      ≤ ∫ z, |g z| * (C * volume.real (Metric.ball (0 : ℂ) r)) := by
        refine integral_mono hint.integral_prod_left (hg.abs.mul_const _) fun z => ?_
        show ∫ w, S.indicator (fun p : ℂ × ℂ => |g p.1| * |g p.2|) (z, w) ≤ _
        rw [hsec z, integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hin z) (abs_nonneg _)
    _ = C * volume.real (Metric.ball (0 : ℂ) r) * ∫ z, |g z| := by
        rw [integral_mul_const]
        ring

end LatticeProb.Gauss

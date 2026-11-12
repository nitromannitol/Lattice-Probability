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
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  set a := α * Real.log (R / ε) with ha
  set F : ℝ → ℝ := (Set.Iic a).indicator fun x => rexp (γ * x) with hFdef
  set W : ℝ → ℝ := GaussIndep.expWeight γ (Real.log 2).toNNReal with hWdef
  have hF : Measurable F :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  have hW : Measurable W := GaussIndep.measurable_expWeight γ _
  set TH : Ω → ℂ → ℝ := fun ω z => F (H ω ε z - H ω R 0) * W (H ω (ε / 2) z - H ω ε z) with hTH
  have hTae : ∀ z, (fun ω => F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z)) =ᵐ[P]
      fun ω => TH ω z := by
    intro z
    filter_upwards [hHae] with ω hω
    simp only [hTH, hω]
  have e1 : ∫ ω, (∫ z, g z * (F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z)) ∂ν) ^ 2 ∂P =
      ∫ ω, (∫ z, g z * TH ω z ∂ν) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hHae] with ω hω
    simp only [hTH, hω]
  rw [e1]
  have hS : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε} :=
    measurableSet_lt (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable measurable_const
  have hsq2 : ∀ z, (fun ω => (F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z)) ^ 2) =ᵐ[P]
      fun ω => TH ω z ^ 2 := by
    intro z
    filter_upwards [hTae z] with ω hω
    rw [hω]
  refine FiniteRange.integral_sq_integral_le ?_ hgm hg hS ?_ ?_ ?_
  · have hm1 : Measurable fun q : Ω × ℂ => H q.1 ε q.2 := (hHm ε hε).comp measurable_swap
    have hm2 : Measurable fun q : Ω × ℂ => H q.1 (ε / 2) q.2 := (hHm (ε / 2) (by positivity)).comp measurable_swap
    have hm3 : Measurable fun q : Ω × ℂ => H q.1 R 0 :=
      (hHm R hR).comp (measurable_const.prodMk measurable_fst)
    exact (hF.comp (hm1.sub hm3)).mul (hW.comp (hm2.sub hm1))
  · intro z hz
    exact (hh.integrable_thin_sq hε (hgR z hz) γ a).congr (hsq2 z)
  · intro z hz
    rw [← integral_congr_ae (hsq2 z)]
    exact hh.integral_thin_sq_le hε (hgR z hz) hα
  · intro z w hz hw hzw
    have h2 : 2 * ε ≤ ‖z - w‖ := by simpa [not_lt] using hzw
    have hprod : (fun ω => F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω (ε / 2) z - hcirc ω ε z) *
        (F (hcirc ω ε w - hcirc ω R 0) * W (hcirc ω (ε / 2) w - hcirc ω ε w))) =ᵐ[P]
        fun ω => TH ω z * TH ω w := by
      filter_upwards [hTae z, hTae w] with ω h1 h2
      rw [h1, h2]
    rw [← integral_congr_ae hprod]
    exact hh.integral_thin_mul_thin_eq_zero hε (hgR z hz) (hgR w hw) h2 γ a

end LatticeProb.Gauss.IsWholePlaneGFF

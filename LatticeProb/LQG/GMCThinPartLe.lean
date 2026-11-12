import LatticeProb.LQG.GMCThinPart
import LatticeProb.LQG.GMCPointwiseMomentsLe

/-!
# Thin points of the circle-average approximations at a general scale ratio

This is the version of `LatticeProb.LQG.GMCThinPart` for the increment `D_z = h_s(z) - h_ε(z)` between the circle
averages of radii `s` and `ε`, for arbitrary `0 < s ≤ ε`, instead of the dyadic increment `s = ε / 2`.
With `X_z = h_ε(z) - h_R(0)`, `L = log (R / ε)` and
`T_z = e^{γ X_z} 1{X_z ≤ α L} W(D_z)`, where `W(d) = (s / ε)^{γ²/2} e^{γ d} - 1` has variance `(ε / s)^{γ²} - 1`
(`GaussIndep.expWeight γ (log (ε / s))`):

* `integral_sq_integral_thin_le_of_le`: for `α ≤ 2γ` and `g` supported where `‖z‖ + ε ≤ R`,
  `E[(∫ g T dν)²] ≤ ((ε/s)^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)} ∫∫_{‖z - w‖ < 2ε} |g(z)| |g(w)| dν(z) dν(w)`;
* `integral_abs_integral_thin_le_of_le`: the resulting L¹ bound `E|∫ g T dν| ≤ (B I / t + t) / 2`, `t > 0`.

The area estimate `integral_indicator_norm_sub_lt_le` of `GMCThinPart` does not involve the increment.
-/

open MeasureTheory ProbabilityTheory Real Function
open scoped ENNReal NNReal

namespace LatticeProb.Gauss.IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Thin points: `T_z = e^{γ X_z} 1{X_z ≤ a} W(D_z)` is square integrable. -/
theorem integrable_thin_sq_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) {z : ℂ} (hz : ‖z‖ + ε ≤ R) (γ a : ℝ) :
    Integrable (fun ω => ((Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z)) ^ 2) P := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hm : Measurable ((Set.Iic a).indicator fun x => rexp (γ * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  refine GaussIndep.integrable_mul_expWeight_sq (hh.hasLaw_incr_le hs hsε z)
    (hh.indepFun_recentred_incr_le hs hsε hz) hm ?_ γ
  have hI := (integrable_exp_mul_gaussianReal (μ := 0)
    (v := (Real.log (R / ε)).toNNReal) (2 * γ)).indicator (measurableSet_Iic (a := a))
  refine ((hh.hasLaw_recentred_circle hε hz).integrable_comp hI).congr (ae_of_all _ fun ω => ?_)
  exact (GaussTail.indicator_exp_mul_sq _ γ _).symm

/-- The thin-point integrand `T_z = e^{γ X_z} 1{X_z ≤ α L} W(D_z)` has a modification `T'` jointly measurable in
`(ω, z)`, and `T'_z` inherits the pointwise bounds: square integrability,
`E[T'_z²] ≤ ((ε/s)^{γ²} - 1) e^{L (2γ² - (2γ-α)²/2)}` and `E[T'_z T'_w] = 0` for `2ε ≤ |z - w|`. -/
theorem exists_measurable_thin_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) (hR : 0 < R) {γ α : ℝ} (hα : α ≤ 2 * γ) :
    ∃ TH : Ω → ℂ → ℝ, (Measurable fun q : Ω × ℂ => TH q.1 q.2) ∧
      (∀ᵐ ω ∂P, ∀ z, (Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z) = TH ω z) ∧
      (∀ z, ‖z‖ + ε ≤ R → Integrable (fun ω => TH ω z ^ 2) P) ∧
      (∀ z, ‖z‖ + ε ≤ R → ∫ ω, TH ω z ^ 2 ∂P ≤
        (rexp (γ ^ 2 * Real.log (ε / s)) - 1) *
          rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2))) ∧
      (∀ z w, ‖z‖ + ε ≤ R → ‖w‖ + ε ≤ R → 2 * ε ≤ ‖z - w‖ → ∫ ω, TH ω z * TH ω w ∂P = 0) := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  obtain ⟨H, -, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  set a := α * Real.log (R / ε) with ha
  set F : ℝ → ℝ := (Set.Iic a).indicator fun x => rexp (γ * x) with hFdef
  set W : ℝ → ℝ := GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal with hWdef
  have hF : Measurable F :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  have hW : Measurable W := GaussIndep.measurable_expWeight γ _
  set TH : Ω → ℂ → ℝ := fun ω z => F (H ω ε z - H ω R 0) * W (H ω s z - H ω ε z) with hTH
  have hae : ∀ᵐ ω ∂P, ∀ z, F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω s z - hcirc ω ε z) = TH ω z := by
    filter_upwards [hHae] with ω hω z
    simp only [hTH, hω]
  have hTae : ∀ z, (fun ω => F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω s z - hcirc ω ε z)) =ᵐ[P]
      fun ω => TH ω z := fun z => hae.mono fun ω hω => hω z
  have hsq2 : ∀ z, (fun ω => (F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω s z - hcirc ω ε z)) ^ 2) =ᵐ[P]
      fun ω => TH ω z ^ 2 := fun z => hae.mono fun ω hω => by simp only [hω z]
  refine ⟨TH, ?_, hae, fun z hz => (hh.integrable_thin_sq_of_le hs hsε hz γ a).congr (hsq2 z), fun z hz => ?_,
    fun z w hz hw hzw => ?_⟩
  · have hm1 : Measurable fun q : Ω × ℂ => H q.1 ε q.2 := (hHm ε hε).comp measurable_swap
    have hm2 : Measurable fun q : Ω × ℂ => H q.1 s q.2 := (hHm s hs).comp measurable_swap
    have hm3 : Measurable fun q : Ω × ℂ => H q.1 R 0 :=
      (hHm R hR).comp (measurable_const.prodMk measurable_fst)
    exact (hF.comp (hm1.sub hm3)).mul (hW.comp (hm2.sub hm1))
  · rw [← integral_congr_ae (hsq2 z)]
    exact hh.integral_thin_sq_le_of_le hs hsε hz hα
  · have hprod : (fun ω => F (hcirc ω ε z - hcirc ω R 0) * W (hcirc ω s z - hcirc ω ε z) *
        (F (hcirc ω ε w - hcirc ω R 0) * W (hcirc ω s w - hcirc ω ε w))) =ᵐ[P]
        fun ω => TH ω z * TH ω w := by
      filter_upwards [hTae z, hTae w] with ω h1 h2
      rw [h1, h2]
    rw [← integral_congr_ae hprod]
    exact hh.integral_thin_mul_thin_eq_zero_le hs hsε hz hw hzw γ a

/-- **Thin points, integrated over the plane.** For `α ≤ 2γ`, `L = log (R / ε)` and an integrable weight `g`
supported where `‖z‖ + ε ≤ R`,
`E[(∫ g(z) e^{γ X_z} 1{X_z ≤ α L} W(D_z) dν(z))²]
  ≤ ((ε/s)^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)} ∫_{‖z - w‖ < 2ε} |g(z)| |g(w)| d(ν ⊗ ν)(z, w)`. -/
theorem integral_sq_integral_thin_le_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g)
    (hg : Integrable g ν) (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) :
    ∫ ω, (∫ z, g z * ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z)) ∂ν) ^ 2 ∂P ≤
      (rexp (γ ^ 2 * Real.log (ε / s)) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
        ∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν) := by
  have := hh.isProbabilityMeasure
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  obtain ⟨TH, hTm, hae, hT2, hTB, hTo⟩ := hh.exists_measurable_thin_of_le hs hsε hR hα
  have hS : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε} :=
    measurableSet_lt (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable measurable_const
  refine (le_of_eq (integral_congr_ae ?_)).trans (FiniteRange.integral_sq_integral_le hTm hgm hg hS
    (fun z hz => hT2 z (hgR z hz)) (fun z hz => hTB z (hgR z hz))
    (fun z w hz hw hzw => hTo z w (hgR z hz) (hgR w hw) (by simpa [not_lt] using hzw)))
  filter_upwards [hae] with ω hω
  simp only [hω]

/-- The square of the integrated thin part is integrable. -/
theorem integrable_sq_integral_thin_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g)
    (hg : Integrable g ν) (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) :
    Integrable (fun ω => (∫ z, g z * ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z)) ∂ν) ^ 2) P := by
  have := hh.isProbabilityMeasure
  obtain ⟨TH, hTm, hae, hT2, hTB, -⟩ := hh.exists_measurable_thin_of_le hs hsε hR hα
  refine (FiniteRange.integrable_sq_integral hTm hgm hg (fun z hz => hT2 z (hgR z hz))
    (fun z hz => hTB z (hgR z hz))).congr ?_
  filter_upwards [hae] with ω hω
  simp only [hω]

/-- **Thin points, L¹ bound.** With `B` the second-moment bound of `integral_sq_integral_thin_le_of_le` and
`I = ∫_{‖z - w‖ < 2ε} |g(z)| |g(w)|`, `E|∫ g T dν| ≤ (B I / t + t) / 2` for every `t > 0`. -/
theorem integral_abs_integral_thin_le_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) (hR : 0 < R) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ} (hgm : Measurable g)
    (hg : Integrable g ν) (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) {t : ℝ}
    (ht : 0 < t) :
    ∫ ω, |∫ z, g z * ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x))
          (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z)) ∂ν| ∂P ≤
      ((rexp (γ ^ 2 * Real.log (ε / s)) - 1) *
        rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) *
        (∫ p, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) / t +
          t) / 2 := by
  have := hh.isProbabilityMeasure
  refine (FiniteRange.integral_abs_le_of_integrable_sq
    (hh.integrable_sq_integral_thin_of_le hs hsε hR ν hgm hg hgR hα) ht).trans ?_
  gcongr
  exact hh.integral_sq_integral_thin_le_of_le hs hsε hR ν hgm hg hgR hα

end LatticeProb.Gauss.IsWholePlaneGFF

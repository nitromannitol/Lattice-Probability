import Mathlib
import LatticeProb.LQG.MarkedRootingApprox
import LatticeProb.LQG.MarkedRootingCov
import LatticeProb.LQG.MassFunctional
import LatticeProb.LQG.WeylOffOrigin

/-!
# The approximate Palm identity for products of a test function and a cylinder functional

For a whole-plane Gaussian free field `h` and the approximation `λ_ε = ε^{γ²/2} e^{γ h_ε(z)} dz` of the
`γ`-Liouville quantum gravity measure, `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lintegral_exp_circle_mul_eq`
tilts by `exp (γ h_ε(z))` and shifts the family of all observables by `γ Cov (·, h_ε(z))`. Here this is put into
real-valued form for the functionals used in the marked rooting identity: a nonnegative continuous compactly
supported function `g` of the root, times a bounded nonnegative continuous function `F` of finitely many pairings
`(h, φ_i)`:
`E [F ((h, φ_i)_i) ∫ g dλ_ε] = ∫ g(z) exp (γ² (Var h_ε(z) + log ε) / 2) E [F ((h, φ_i) + γ Cov ((h, φ_i), h_ε(z)))_i] dz`.
The limit `ε → 0` of the right-hand side is taken using the covariance limits of
`LatticeProb.LQG.MarkedRootingCov`.

## Main statements

* `LatticeProb.Gauss.IsWholePlaneGFF.integral_mul_integral_lqgApprox_eq`
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace LatticeProb.Gauss

/-- The circle average `z ↦ avg_{∂B_ε(z)} log max(|·|, 1)` is continuous. -/
theorem continuous_circleAverage_wholePlaneNormalization (ε : ℝ) :
    Continuous fun z : ℂ => Real.circleAverage wholePlaneNormalization z ε :=
  (Section6.continuous_circleAverage_radius_center continuous_wholePlaneNormalization).comp
    (continuous_const.prodMk continuous_id)

/-- The variance of the circle average is continuous in the centre. -/
theorem continuous_wholePlaneGFFCov_circle_self {ε : ℝ} (hε : 0 < ε) :
    Continuous fun z : ℂ => wholePlaneGFFCov (.circle ε z) (.circle ε z) := by
  have e : (fun z : ℂ => wholePlaneGFFCov (.circle ε z) (.circle ε z)) =
      fun z => 2 * Real.circleAverage wholePlaneNormalization z ε - Real.log ε := by
    funext z
    exact wholePlaneGFFCov_circle_self_eq_sub_log hε z
  rw [e]
  exact (continuous_const.mul (continuous_circleAverage_wholePlaneNormalization ε)).sub continuous_const

/-- The covariance of a pairing with the circle average `h_ε(z)` is measurable in the centre `z`. -/
theorem measurable_wholePlaneGFFCov_pairing_circle {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {ε : ℝ}
    (hε : 0 < ε) : Measurable fun z : ℂ => wholePlaneGFFCov (.pairing φ) (.circle ε z) := by
  have e : (fun z : ℂ => wholePlaneGFFCov (.pairing φ) (.circle ε z)) = fun z =>
      ∫ x, φ x * (wholePlaneNormalization x + Real.circleAverage wholePlaneNormalization z ε -
        Real.log (max ε ‖z - x‖)) := by
    funext z
    exact wholePlaneGFFCov_pairing_circle_eq φ hε z
  rw [e]
  have hc : Continuous fun p : ℂ × ℂ => p.2 |> fun x => φ x * (wholePlaneNormalization x +
      Real.circleAverage wholePlaneNormalization p.1 ε - Real.log (max ε ‖p.1 - x‖)) := by
    refine (hφ.1.continuous.comp continuous_snd).mul ?_
    refine ((continuous_wholePlaneNormalization.comp continuous_snd).add
      ((continuous_circleAverage_wholePlaneNormalization ε).comp continuous_fst)).sub ?_
    exact (continuous_const.max ((continuous_fst.sub continuous_snd).norm)).log
      (fun p => (lt_of_lt_of_le hε (le_max_left _ _)).ne')
  exact (hc.stronglyMeasurable.integral_prod_right').measurable

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Almost surely, `z ↦ h_ε(z)` is continuous for a fixed radius `ε > 0`. -/
theorem ae_continuous_circle_slice (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Continuous (hcirc ω ε) := by
  filter_upwards [hh.ae_continuousOn_circle] with ω hω
  exact hω.comp_continuous (f := fun z : ℂ => (ε, z)) (continuous_const.prodMk continuous_id)
    fun z => ⟨hε, Set.mem_univ z⟩

/-- **Approximate Palm identity for a product functional.** For `ε > 0`, a nonnegative continuous compactly
supported `g` and a bounded nonnegative continuous `F` of the pairings with finitely many test functions `φ i`,
`E [F ((h, φ_i)_i) ∫ g dλ_ε] = ∫ g(z) exp (γ² (Var h_ε(z) + log ε) / 2)
  E [F ((h, φ_i) + γ Cov ((h, φ_i), h_ε(z)))_i] dz`, with `λ_ε = ε^{γ²/2} e^{γ h_ε(z)} dz`. -/
theorem integral_mul_integral_lqgApprox_eq (hh : IsWholePlaneGFF P hC hcirc) {γ ε : ℝ} (hε : 0 < ε)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z)
    {m : ℕ} {φ : Fin m → ℂ → ℝ} (hφ : ∀ i, IsTestFunction Set.univ (φ i))
    {F : (Fin m → ℝ) → ℝ} (hFc : Continuous F) {M : ℝ} (hFM : ∀ x, F x ≤ M) (hF0 : ∀ x, 0 ≤ F x) :
    ∫ ω, F (fun i => hC ω (φ i)) * ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) ε) ∂P =
      ∫ z, g z * Real.exp (γ ^ 2 * (wholePlaneGFFCov (.circle ε z) (.circle ε z) + Real.log ε) / 2) *
        ∫ ω, F (fun i => hC ω (φ i) + γ * wholePlaneGFFCov (.pairing (φ i)) (.circle ε z)) ∂P := by
  have hP := hh.isProbabilityMeasure
  have hpm := hh.measurable_observablePath
  let c : (GFFObservable.Admissible → ℝ) → (Fin m → ℝ) := fun p i => p ⟨.pairing (φ i), hφ i⟩
  have hcm : Measurable c := measurable_pi_iff.2 fun i => measurable_pi_apply _
  let Φ : ℂ → (GFFObservable.Admissible → ℝ) → ℝ≥0∞ := fun z p =>
    ENNReal.ofReal (g z) * ENNReal.ofReal (F (c p))
  have hΦ : Measurable fun q : ℂ × (GFFObservable.Admissible → ℝ) => Φ q.1 q.2 :=
    (ENNReal.measurable_ofReal.comp (hgc.measurable.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (hFc.measurable.comp (hcm.comp measurable_snd)))
  have h1 := hh.lintegral_lintegral_exp_circle_mul_eq (γ := γ) hε Set.univ hΦ
  simp only [Measure.restrict_univ] at h1
  -- the left-hand side
  set B : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, ENNReal.ofReal (Real.exp (γ * hcirc ω ε z) * g z) with hB
  have hL : ∀ ω, ∫⁻ z, ENNReal.ofReal (Real.exp (γ * hcirc ω ε z)) * Φ z (observablePath hC hcirc ω) =
      ENNReal.ofReal (F (fun i => hC ω (φ i))) * B ω := by
    intro ω
    rw [hB, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    show ENNReal.ofReal (Real.exp (γ * hcirc ω ε z)) * (ENNReal.ofReal (g z) *
        ENNReal.ofReal (F (fun i => hC ω (φ i)))) = ENNReal.ofReal (F (fun i => hC ω (φ i))) *
          ENNReal.ofReal (Real.exp (γ * hcirc ω ε z) * g z)
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  rw [lintegral_congr hL] at h1
  have hBm : AEMeasurable B P := by
    have hf : AEMeasurable (fun p : Ω × ℂ => ENNReal.ofReal (Real.exp (γ * hcirc p.1 ε p.2) * g p.2))
        (P.prod volume) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((Real.measurable_exp.comp_aemeasurable
          ((hh.aemeasurable_circle_uncurry hε volume).const_mul γ)).mul
          (hgc.measurable.comp measurable_snd).aemeasurable)
    exact hf.lintegral_prod_right'
  have hFm : Measurable fun ω => F (fun i => hC ω (φ i)) :=
    hFc.measurable.comp (measurable_pi_iff.2 fun i => hh.measurable_pairing _ (hφ i))
  have hBfin : ∀ᵐ ω ∂P, B ω < ∞ := by
    filter_upwards [hh.ae_continuous_circle_slice hε] with ω hω
    have hc : Continuous fun z => Real.exp (γ * hcirc ω ε z) * g z :=
      (Real.continuous_exp.comp (continuous_const.mul hω)).mul hgc
    have hcs : HasCompactSupport fun z => Real.exp (γ * hcirc ω ε z) * g z :=
      hgs.mul_left
    exact (hc.integrable_of_hasCompactSupport hcs).lintegral_lt_top
  -- the right-hand side
  set s : Fin m → ℂ → ℝ := fun i z => wholePlaneGFFCov (.pairing (φ i)) (.circle ε z) with hs
  set V : ℂ → ℝ := fun z => wholePlaneGFFCov (.circle ε z) (.circle ε z) with hV
  set E : ℂ → ℝ := fun z => ∫ ω, F (fun i => hC ω (φ i) + γ * s i z) ∂P with hE
  have hsm : ∀ i, Measurable (s i) := fun i => measurable_wholePlaneGFFCov_pairing_circle (hφ i) hε
  have hFcm : Measurable fun q : ℂ × Ω => F (fun i => hC q.2 (φ i) + γ * s i q.1) :=
    hFc.measurable.comp (measurable_pi_iff.2 fun i =>
      ((hh.measurable_pairing _ (hφ i)).comp measurable_snd).add (((hsm i).comp measurable_fst).const_mul γ))
  have hEm : Measurable E := (hFcm.stronglyMeasurable.integral_prod_right').measurable
  have hint : ∀ z, Integrable (fun ω => F (fun i => hC ω (φ i) + γ * s i z)) P := fun z =>
    Integrable.of_bound (C := max M 0)
      (hFcm.comp measurable_prodMk_left).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
        exact (hFM _).trans (le_max_left _ _))
  have hR : ∀ z, ∫⁻ ω, Φ z (fun o => observablePath hC hcirc ω o + γ * wholePlaneGFFCov o.1 (.circle ε z)) ∂P =
      ENNReal.ofReal (g z) * ENNReal.ofReal (E z) := by
    intro z
    calc ∫⁻ ω, Φ z (fun o => observablePath hC hcirc ω o + γ * wholePlaneGFFCov o.1 (.circle ε z)) ∂P
        = ∫⁻ ω, ENNReal.ofReal (g z) * ENNReal.ofReal (F (fun i => hC ω (φ i) + γ * s i z)) ∂P := rfl
      _ = ENNReal.ofReal (g z) * ∫⁻ ω, ENNReal.ofReal (F (fun i => hC ω (φ i) + γ * s i z)) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (g z) * ENNReal.ofReal (E z) := by
          rw [hE, ofReal_integral_eq_lintegral_ofReal (hint z) (Eventually.of_forall fun ω => hF0 _)]
  simp only [hR] at h1
  have hEnn : ∀ z, 0 ≤ E z := fun z => integral_nonneg fun ω => hF0 _
  have hR2 : ∀ z, ENNReal.ofReal (Real.exp (γ ^ 2 * wholePlaneGFFCov (.circle ε z) (.circle ε z) / 2)) *
      (ENNReal.ofReal (g z) * ENNReal.ofReal (E z)) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * V z / 2) * g z * E z) := by
    intro z
    rw [ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (hg0 z)), ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact (mul_assoc _ _ _).symm
  simp only [hR2] at h1
  have h2 := congrArg ENNReal.toReal h1
  have hi1 := integral_toReal (f := fun ω => ENNReal.ofReal (F (fun i => hC ω (φ i))) * B ω)
    (hFm.ennreal_ofReal.aemeasurable.mul hBm)
    (by filter_upwards [hBfin] with ω hω using ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω)
  have hVm : Measurable V := (continuous_wholePlaneGFFCov_circle_self hε).measurable
  have hi2 := integral_eq_lintegral_of_nonneg_ae (μ := volume)
    (f := fun z => Real.exp (γ ^ 2 * V z / 2) * g z * E z)
    (Eventually.of_forall fun z => mul_nonneg (mul_nonneg (Real.exp_pos _).le (hg0 z)) (hEnn z))
    (((Real.measurable_exp.comp ((hVm.const_mul (γ ^ 2)).div_const 2)).mul hgc.measurable).mul
      hEm).aestronglyMeasurable
  rw [← hi1, ← hi2] at h2
  -- the left-hand side
  have hLHS : ∀ᵐ ω ∂P, F (fun i => hC ω (φ i)) * ∫ z, g z ∂(LQG.lqgApprox γ (hcirc ω) ε) =
      ε ^ (γ ^ 2 / 2) * (ENNReal.ofReal (F (fun i => hC ω (φ i))) * B ω).toReal := by
    filter_upwards [hh.ae_continuous_circle_slice hε] with ω hω
    have hc : Continuous fun z => Real.exp (γ * hcirc ω ε z) * g z :=
      (Real.continuous_exp.comp (continuous_const.mul hω)).mul hgc
    rw [LQG.WeylOffOriginDerived.integral_lqgApprox hε.le hω.measurable, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hF0 _), hB,
      ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z =>
        mul_nonneg (Real.exp_pos _).le (hg0 z)) hc.aestronglyMeasurable]
    have : ∫ z, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z) * g z =
        ε ^ (γ ^ 2 / 2) * ∫ z, Real.exp (γ * hcirc ω ε z) * g z := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      exact mul_assoc _ _ _
    rw [this]
    ring
  rw [integral_congr_ae hLHS, integral_const_mul, h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show ε ^ (γ ^ 2 / 2) * (Real.exp (γ ^ 2 * V z / 2) * g z * E z) =
    g z * Real.exp (γ ^ 2 * (V z + Real.log ε) / 2) * E z
  have : Real.exp (γ ^ 2 * (V z + Real.log ε) / 2) =
      Real.exp (γ ^ 2 * V z / 2) * ε ^ (γ ^ 2 / 2) := by
    rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
    congr 1
    ring
  rw [this]
  ring

end IsWholePlaneGFF

end LatticeProb.Gauss

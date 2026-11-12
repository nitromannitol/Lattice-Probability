import Mathlib
import LatticeProb.Gauss.GFFCovSymm
import LatticeProb.Gauss.UncorrelatedIndependence
import LatticeProb.Gauss.CircleAverageApprox
import LatticeProb.LQG.LQGMeasureLocality2
import LatticeProb.LQG.LQGBallMassLowerTail

/-! # A circle average of radius `R ≥ 1` is independent of the field inside the unit disc

For the whole-plane GFF `h` (normalised so that its unit circle average vanishes) and `R ≥ 1`, the circle average
`h_R(0)` is uncorrelated with every pairing `(h, φ)` with `φ` a test function supported in the open unit disc: the
logarithmic kernel `log (max(|x|,1) max(|y|,1) / |x - y|)` averaged over `|y| = R` is `log R - log R = 0` for
`|x| < 1 ≤ R`. Since the family is jointly Gaussian, `h_R(0)` is independent of the σ-algebra of the restriction of `h`
to any set inside the unit disc, hence of the mass of any open subset of the disc under the LQG measure (locality).

Main results:
* `circleAverage_wholePlaneCov_eq_zero`: the averaged kernel vanishes for `|x| < 1 ≤ R`.
* `wholePlaneGFFCov_circle_pairing_eq_zero`: `Cov(h_R(0), (h, φ)) = 0` for `φ` supported in the unit disc.
* `IsWholePlaneGFF.indep_circle_fieldSigmaAlgebra`: `σ(h_R(0))` is independent of `σ(h|_U)` for `U ⊆ B(0,1)`.
* `IsWholePlaneGFF.indepFun_circle_measure_ball`: `h_R(0)` is independent of `μ(B(0, s))`, `s ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb.Gauss

/-- For `‖x‖ < 1 ≤ R`, the kernel `wholePlaneCov x ·` has zero average over the circle `∂B_R(0)`. -/
theorem circleAverage_wholePlaneCov_eq_zero {R : ℝ} (hR : 1 ≤ R) {x : ℂ} (hx : ‖x‖ < 1) :
    Real.circleAverage (fun y => wholePlaneCov x y) 0 R = 0 := by
  have hR0 : 0 < R := by linarith
  have hcongr : Set.EqOn (fun y => wholePlaneCov x y) (fun y => Real.log R - Real.log ‖y - x‖)
      (sphere (0 : ℂ) |R|) := by
    intro y hy
    have hy' : ‖y‖ = R := by
      rw [mem_sphere_zero_iff_norm] at hy
      rw [hy, abs_of_pos hR0]
    have hne : ‖x - y‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      rintro rfl
      linarith
    simp only [wholePlaneCov, max_eq_right hx.le, hy', max_eq_left hR, one_mul]
    rw [Real.log_div hR0.ne' hne, norm_sub_rev]
  have hfun : (fun y : ℂ => Real.log R - Real.log ‖y - x‖) =
      (fun _ : ℂ => Real.log R) - fun y => Real.log ‖y - x‖ := rfl
  rw [Real.circleAverage_congr_sphere hcongr, hfun,
    Real.circleAverage_sub (circleIntegrable_const _ _ _) (circleIntegrable_log_norm_sub_const R),
    Real.circleAverage_const, circleAverage_log_norm_sub_eq_log_max hR0]
  have : max R ‖(0 : ℂ) - x‖ = R := by
    rw [zero_sub, norm_neg]
    exact max_eq_left (by linarith)
  rw [this]
  ring

/-- `Cov(h_R(0), (h, φ)) = 0` for `R ≥ 1` and `φ` a test function supported in the open unit disc. -/
theorem wholePlaneGFFCov_circle_pairing_eq_zero {R : ℝ} (hR : 1 ≤ R) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction univ ψ) (hsupp : ∀ x, ψ x ≠ 0 → ‖x‖ < 1) :
    wholePlaneGFFCov (.circle R 0) (.pairing ψ) = 0 := by
  have hR0 : 0 < R := by linarith
  rw [GFFCovSymm.cp_symm hR0 hψ]
  simp only [wholePlaneGFFCov, GFFObservable.smear]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x => ?_)
  by_cases h : ψ x = 0
  · simp [h]
  · simp only [Pi.zero_apply]
    rw [circleAverage_wholePlaneCov_eq_zero hR (hsupp x h), mul_zero]

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Independence of the large circle average from the pairings inside the unit disc.** For `R ≥ 1`, `h_R(0)` is
independent of the family of pairings `(h, φ)` with `φ` a test function supported in `B(0,1)`. -/
theorem indepFun_circle_pairings (hh : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 1 ≤ R) :
    IndepFun (fun ω => hcirc ω R 0)
      (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction (ball (0 : ℂ) 1) φ}) => hC ω φ.1) P := by
  have hR0 : 0 < R := by linarith
  have hφu : ∀ φ : {φ : ℂ → ℝ // IsTestFunction (ball (0 : ℂ) 1) φ}, IsTestFunction univ φ.1 :=
    fun φ => ⟨φ.2.1, φ.2.2.1, subset_univ _⟩
  refine GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hh.isGaussianProcess
    (Submodule.subset_span ⟨⟨.circle R 0, hR0⟩, rfl⟩)
    (B := fun (φ : {φ : ℂ → ℝ // IsTestFunction (ball (0 : ℂ) 1) φ}) ω => hC ω φ.1)
    (fun φ => Submodule.subset_span ⟨⟨.pairing φ.1, hφu φ⟩, rfl⟩) (fun φ => ?_)
  have h1 := hh.covariance_eq (.circle R 0) (.pairing φ.1) hR0 (hφu φ)
  refine h1.trans (wholePlaneGFFCov_circle_pairing_eq_zero hR (hφu φ) fun x hx => ?_)
  have : x ∈ tsupport φ.1 := subset_tsupport _ hx
  simpa using φ.2.2.2 this

/-- **Independence of `σ(h_R(0))` from `σ(h|_U)`** for `U ⊆ B(0,1)` and `R ≥ 1`. -/
theorem indep_circle_fieldSigmaAlgebra (hh : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 1 ≤ R)
    {U : Set ℂ} (hU : U ⊆ ball 0 1) :
    Indep (MeasurableSpace.comap (fun ω => hcirc ω R 0) inferInstance) (fieldSigmaAlgebra 0 hC U) P := by
  have hind := hh.indepFun_circle_pairings hR
  refine indep_of_indep_of_le_right hind ?_
  refine iSup₂_le fun φ hφ => ?_
  have hφ' : IsTestFunction (ball (0 : ℂ) 1) φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hU⟩
  have hm : Measurable[MeasurableSpace.comap
      (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction (ball (0 : ℂ) 1) φ}) => hC ω φ.1)
      MeasurableSpace.pi] (fun ω => hC ω φ) :=
    fun s hs => ⟨{f | f (⟨φ, hφ'⟩ : {φ : ℂ → ℝ // IsTestFunction (ball (0 : ℂ) 1) φ}) ∈ s},
      measurable_pi_apply _ hs, rfl⟩
  have e : (fun ω => fieldPairing 0 (hC ω) φ) = fun ω => hC ω φ := by
    funext ω
    simp [fieldPairing]
  rw [e]
  exact hm.comap_le

/-- **Independence of `h_R(0)` from the LQG mass of an open set inside the unit disc.** For `R ≥ 1`, `0 < γ < 2`, `U`
open with `U ⊆ B(0,1)`, the circle average `h_R(0)` is independent of `μ(U)`, `μ` the LQG measure of `h`. -/
theorem indepFun_circle_measure_open {γ : ℝ} {μ : Ω → Measure ℂ} (hh : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hμ : LQG.IsLQGMeasure P γ hcirc μ) {R : ℝ} (hR : 1 ≤ R)
    {U : Set ℂ} (hUo : IsOpen U) (hU : U ⊆ ball 0 1) :
    IndepFun (fun ω => hcirc ω R 0) (fun ω => μ ω U) P := by
  have hα : (0 : ℝ) < LQG.lqgQ γ := by unfold LQG.lqgQ; positivity
  obtain ⟨Y, hYm, hYae⟩ := LQG.lqgLocality_of_gff P γ 0 hC hcirc hh hγ0 hγ2 hα μ
    (LQG.isLQGMeasureOfField_zero hμ) U hUo
  have hind := hh.indep_circle_fieldSigmaAlgebra hR hU
  have hY : IndepFun (fun ω => hcirc ω R 0) Y P :=
    indep_of_indep_of_le_right hind (measurable_iff_comap_le.1 hYm)
  exact hY.congr Filter.EventuallyEq.rfl (hYae.mono fun ω h => h.symm)

end IsWholePlaneGFF

end LatticeProb.Gauss

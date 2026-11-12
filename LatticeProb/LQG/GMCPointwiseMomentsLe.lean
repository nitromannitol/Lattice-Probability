import LatticeProb.LQG.GMCPointwiseMoments

/-!
# Pointwise exponential moments of circle averages at a general scale ratio

This is the version of `LatticeProb.LQG.GMCPointwiseMoments` for the increment `D = h_s(z) - h_ε(z)` between the
circle averages of radii `s` and `ε`, for arbitrary `0 < s ≤ ε`, instead of the dyadic increment `s = ε / 2`.
With `X = h_ε(z) - h_R(0)` (law `N(0, log (R / ε))`) the increment `D` has law `N(0, log (ε / s))` and is independent
of `X` (and of `(X_z, X_w, D_w)` when `2 ε ≤ |z - w|`). The martingale increment
`T = e^{γ X} 1{X ≤ a} W(D)` with `W(d) = (s / ε)^{γ²/2} e^{γ d} - 1` satisfies `E[T_z T_w] = 0` for `2 ε ≤ |z - w|` and
`E[T²] ≤ ((ε / s)^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}`.

## Main results

* `covariance_incr_recentred_le`, `variance_incr_le`, `hasLaw_incr_le`, `covariance_incr_incr_le`:
  covariance structure of the increments.
* `indepFun_recentred_incr_le`, `indepFun_recentred_incr_of_le_le`: independence statements.
* `integral_thick_mul_exp_incr_le`, `integral_thin_mul_thin_eq_zero_le`, `integral_thin_sq_le_of_le`:
  the thick and thin moment estimates, with `log 2` replaced by `log (ε / s)`.
* `GaussTail.rpow_mul_exp_add_sub_eq_of_le`: the deterministic decomposition
  `s^{γ²/2} e^{γ(x + d)} - ε^{γ²/2} e^{γ x} = ε^{γ²/2} e^{γ x} W(d)`.
-/

open MeasureTheory ProbabilityTheory Real Metric
open scoped ENNReal NNReal

namespace LatticeProb.GaussTail

/-- The deterministic decomposition at a general ratio: with `W(d) = (s/ε)^{γ²/2} e^{γ d} - 1`,
`s^{γ²/2} e^{γ(x + d)} - ε^{γ²/2} e^{γ x} = ε^{γ²/2} e^{γ x} W(d)`, `W` written as the exponential weight of variance
`log (ε / s)`. -/
theorem rpow_mul_exp_add_sub_eq_of_le {s ε : ℝ} (hs : 0 < s) (hsε : s ≤ ε) (γ x d : ℝ) :
    s ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) - ε ^ (γ ^ 2 / 2) * rexp (γ * x) =
      ε ^ (γ ^ 2 / 2) * rexp (γ * x) * GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal d := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hlog : ((Real.log (ε / s)).toNNReal : ℝ) = Real.log (ε / s) :=
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hs).mpr hsε))
  have key : s ^ (γ ^ 2 / 2) * rexp (γ * (x + d)) =
      ε ^ (γ ^ 2 / 2) * rexp (γ * x) * (rexp (-(γ ^ 2 * Real.log (ε / s)) / 2) * rexp (γ * d)) := by
    rw [Real.rpow_def_of_pos hs, Real.rpow_def_of_pos hε, Real.log_div hε.ne' hs.ne', ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [GaussIndep.expWeight, hlog, key]
  ring

end LatticeProb.GaussTail

namespace LatticeProb.Gauss

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Covariance of the increment `h_s(z) - h_ε(z)` with a recentred circle average. -/
theorem covariance_incr_recentred_le (hh : IsWholePlaneGFF P hC hcirc) {s ε ρ R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) (hρ : 0 < ρ) {z w : ℂ} (hz : ‖z‖ + ε ≤ R) (hw : ‖w‖ + ρ ≤ R) :
    cov[fun ω => hcirc ω s z - hcirc ω ε z, fun ω => hcirc ω ρ w - hcirc ω R 0; P] =
      circlePairPotential z ε w ρ - circlePairPotential z s w ρ := by
  have hP := hh.isProbabilityMeasure
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hR : 0 < R := by linarith [norm_nonneg z]
  have hz2 : ‖z‖ + s ≤ R := by linarith
  have e : (fun ω => hcirc ω s z - hcirc ω ε z) =
      fun ω => (hcirc ω s z - hcirc ω R 0) - (hcirc ω ε z - hcirc ω R 0) := by
    funext ω
    ring
  rw [e, covariance_fun_sub_left (hh.memLp_two_circle_sub hs hR z 0) (hh.memLp_two_circle_sub hε hR z 0)
      (hh.memLp_two_circle_sub hρ hR w 0),
    hh.covariance_recentred_circle hs hρ hz2 hw, hh.covariance_recentred_circle hε hρ hz hw]
  ring

/-- The increment at `z` is uncorrelated with the recentred circle averages at `z` of radius at least `ε`. -/
theorem covariance_incr_recentred_same_center_le (hh : IsWholePlaneGFF P hC hcirc) {s ε ρ R : ℝ}
    (hs : 0 < s) (hsε : s ≤ ε) (hερ : ε ≤ ρ) {z : ℂ} (hz : ‖z‖ + ρ ≤ R) :
    cov[fun ω => hcirc ω s z - hcirc ω ε z, fun ω => hcirc ω ρ z - hcirc ω R 0; P] = 0 := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  rw [hh.covariance_incr_recentred_le hs hsε (lt_of_lt_of_le hε hερ) (by linarith) hz,
    circlePairPotential_self_center hε.le, circlePairPotential_self_center hs.le,
    max_eq_left hερ, max_eq_left (hsε.trans hερ), sub_self]

/-- The variance of the increment `h_s(z) - h_ε(z)` is `log (ε / s)`. -/
theorem variance_incr_le (hh : IsWholePlaneGFF P hC hcirc) {s ε : ℝ} (hs : 0 < s) (hsε : s ≤ ε) (z : ℂ) :
    Var[fun ω => hcirc ω s z - hcirc ω ε z; P] = Real.log (ε / s) := by
  have hP := hh.isProbabilityMeasure
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hR : 0 < ‖z‖ + ε := by linarith [norm_nonneg z]
  have hz : ‖z‖ + ε ≤ ‖z‖ + ε := le_rfl
  have hz2 : ‖z‖ + s ≤ ‖z‖ + ε := by linarith
  have mD := hh.memLp_two_circle_sub hs hε z z
  rw [← covariance_self mD.aestronglyMeasurable.aemeasurable]
  have e : (fun ω => hcirc ω s z - hcirc ω ε z) =
      fun ω => (hcirc ω s z - hcirc ω (‖z‖ + ε) 0) - (hcirc ω ε z - hcirc ω (‖z‖ + ε) 0) := by
    funext ω
    ring
  have step : cov[fun ω => hcirc ω s z - hcirc ω ε z,
      fun ω => (hcirc ω s z - hcirc ω (‖z‖ + ε) 0) - (hcirc ω ε z - hcirc ω (‖z‖ + ε) 0); P] =
      Real.log (ε / s) := by
    rw [covariance_fun_sub_right mD (hh.memLp_two_circle_sub hs hR z 0) (hh.memLp_two_circle_sub hε hR z 0),
      hh.covariance_incr_recentred_le hs hsε hs hz hz2, hh.covariance_incr_recentred_le hs hsε hε hz hz,
      circlePairPotential_self_center hε.le, circlePairPotential_self_center hs.le,
      circlePairPotential_self_center hε.le, circlePairPotential_self_center hs.le, max_self, max_self,
      max_eq_right hsε, max_eq_left hsε, Real.log_div hε.ne' hs.ne']
    ring
  rw [← e] at step
  exact step

/-- The increment `h_s(z) - h_ε(z)` has law `N(0, log (ε / s))`. -/
theorem hasLaw_incr_le (hh : IsWholePlaneGFF P hC hcirc) {s ε : ℝ} (hs : 0 < s) (hsε : s ≤ ε) (z : ℂ) :
    HasLaw (fun ω => hcirc ω s z - hcirc ω ε z) (gaussianReal 0 (Real.log (ε / s)).toNNReal) P := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hG := hh.hasGaussianLaw_circle_sub hs hε z z
  exact ⟨hG.aemeasurable, by
    rw [hG.map_eq_gaussianReal, hh.integral_circle_sub hs hε, hh.variance_incr_le hs hsε]⟩

/-- Increments at the same scales over discs `B_ε(z)`, `B_ε(w)` with disjoint interiors are uncorrelated. -/
theorem covariance_incr_incr_le (hh : IsWholePlaneGFF P hC hcirc) {s ε : ℝ} (hs : 0 < s) (hsε : s ≤ ε)
    {z w : ℂ} (hzw : 2 * ε ≤ ‖z - w‖) :
    cov[fun ω => hcirc ω s z - hcirc ω ε z, fun ω => hcirc ω s w - hcirc ω ε w; P] = 0 := by
  have hP := hh.isProbabilityMeasure
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  set R : ℝ := max ‖z‖ ‖w‖ + ε with hRdef
  have hR : 0 < R := by
    have := le_max_left ‖z‖ ‖w‖
    have := norm_nonneg z
    linarith
  have hz : ‖z‖ + ε ≤ R := by
    have := le_max_left ‖z‖ ‖w‖
    linarith
  have hw : ‖w‖ + ε ≤ R := by
    have := le_max_right ‖z‖ ‖w‖
    linarith
  have hw2 : ‖w‖ + s ≤ R := by linarith
  have e : (fun ω => hcirc ω s w - hcirc ω ε w) =
      fun ω => (hcirc ω s w - hcirc ω R 0) - (hcirc ω ε w - hcirc ω R 0) := by
    funext ω
    ring
  rw [e, covariance_fun_sub_right (hh.memLp_two_circle_sub hs hε z z) (hh.memLp_two_circle_sub hs hR w 0)
      (hh.memLp_two_circle_sub hε hR w 0),
    hh.covariance_incr_recentred_le hs hsε hs hz hw2, hh.covariance_incr_recentred_le hs hsε hε hz hw,
    circlePairPotential_of_add_le hε hs.le (by linarith), circlePairPotential_of_add_le hs hs.le (by linarith),
    circlePairPotential_of_add_le hε hε.le (by linarith), circlePairPotential_of_add_le hs hε.le (by linarith)]
  ring

/-- The increment `h_s(z) - h_ε(z)` is independent of the recentred circle average `h_ε(z) - h_R(0)`. -/
theorem indepFun_recentred_incr_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) {z : ℂ} (hz : ‖z‖ + ε ≤ R) :
    IndepFun (fun ω => hcirc ω ε z - hcirc ω R 0) (fun ω => hcirc ω s z - hcirc ω ε z) P := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hR : 0 < R := by linarith [norm_nonneg z]
  have key := GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hh.isGaussianProcess
    (hh.circle_sub_mem_span hs hε z z)
    (B := fun _ : Unit => fun ω => hcirc ω ε z - hcirc ω R 0)
    (fun _ => hh.circle_sub_mem_span hε hR z 0)
    (fun _ => hh.covariance_incr_recentred_same_center_le hs hsε le_rfl hz)
  exact (key.comp (φ := id) (ψ := fun f : Unit → ℝ => f ()) measurable_id (measurable_pi_apply ())).symm

/-- When the discs `B_ε(z)` and `B_ε(w)` have disjoint interiors, the increment at `z` is independent of the
recentred circle averages at `z` and `w` and of the increment at `w`. -/
theorem indepFun_recentred_incr_of_le_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) {z w : ℂ} (hz : ‖z‖ + ε ≤ R) (hw : ‖w‖ + ε ≤ R) (hzw : 2 * ε ≤ ‖z - w‖) :
    IndepFun (fun ω => (hcirc ω ε z - hcirc ω R 0, hcirc ω ε w - hcirc ω R 0,
        hcirc ω s w - hcirc ω ε w)) (fun ω => hcirc ω s z - hcirc ω ε z) P := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hR : 0 < R := by linarith [norm_nonneg z]
  have key := GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hh.isGaussianProcess
    (hh.circle_sub_mem_span hs hε z z)
    (B := ![fun ω => hcirc ω ε z - hcirc ω R 0, fun ω => hcirc ω ε w - hcirc ω R 0,
      fun ω => hcirc ω s w - hcirc ω ε w])
    (by
      intro t
      fin_cases t
      exacts [hh.circle_sub_mem_span hε hR z 0, hh.circle_sub_mem_span hε hR w 0,
        hh.circle_sub_mem_span hs hε w w])
    (by
      intro t
      fin_cases t
      · exact hh.covariance_incr_recentred_same_center_le hs hsε le_rfl hz
      · change cov[fun ω => hcirc ω s z - hcirc ω ε z, fun ω => hcirc ω ε w - hcirc ω R 0; P] = 0
        rw [hh.covariance_incr_recentred_le hs hsε hε hz hw,
          circlePairPotential_of_add_le hε hε.le (by linarith),
          circlePairPotential_of_add_le hs hε.le (by linarith), sub_self]
      · exact hh.covariance_incr_incr_le hs hsε hzw)
  have hm : Measurable fun f : Fin 3 → ℝ => (f 0, f 1, f 2) := by fun_prop
  exact (key.comp (φ := id) (ψ := fun f : Fin 3 → ℝ => (f 0, f 1, f 2)) measurable_id hm).symm

/-- Coarse-to-fine identity on the thick event: `E[e^{γ X} e^{γ D}; X ≥ a] = (ε/s)^{γ²/2} E[e^{γ X}; X ≥ a]`,
written with `(ε/s)^{γ²/2} = e^{γ² log (ε/s) / 2}`. -/
theorem integral_thick_mul_exp_incr_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) {z : ℂ} (hz : ‖z‖ + ε ≤ R) (γ a : ℝ) :
    ∫ ω, (Set.Ici a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        rexp (γ * (hcirc ω s z - hcirc ω ε z)) ∂P =
      (∫ ω, (Set.Ici a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) ∂P) *
        rexp (γ ^ 2 * Real.log (ε / s) / 2) := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hlog : ((Real.log (ε / s)).toNNReal : ℝ) = Real.log (ε / s) :=
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hs).mpr hsε))
  have hm : Measurable ((Set.Ici a).indicator fun x => rexp (γ * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Ici
  have h := GaussIndep.integral_mul_exp_mul (hh.hasLaw_incr_le hs hsε z)
    (hh.hasLaw_recentred_circle hε hz).aemeasurable (hh.indepFun_recentred_incr_le hs hsε hz) hm γ
  rwa [hlog] at h

/-- Thin points, orthogonality: for `T_z = e^{γ X_z} 1{X_z ≤ a} W(D_z)` with the exponential weight
`W(d) = (s/ε)^{γ²/2} e^{γ d} - 1`, `E[T_z T_w] = 0` whenever `2 ε ≤ |z - w|`. -/
theorem integral_thin_mul_thin_eq_zero_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) {z w : ℂ} (hz : ‖z‖ + ε ≤ R) (hw : ‖w‖ + ε ≤ R) (hzw : 2 * ε ≤ ‖z - w‖) (γ a : ℝ) :
    ∫ ω, (Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z) *
        ((Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε w - hcirc ω R 0) *
          GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s w - hcirc ω ε w)) ∂P = 0 := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  set F : ℝ → ℝ := (Set.Iic a).indicator fun x => rexp (γ * x) with hFdef
  have hF : Measurable F :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  set G : ℝ × ℝ × ℝ → ℝ := fun p =>
    F p.1 * (F p.2.1 * GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal p.2.2) with hGdef
  have hG : Measurable G :=
    (hF.comp measurable_fst).mul ((hF.comp (measurable_fst.comp measurable_snd)).mul
      ((GaussIndep.measurable_expWeight γ _).comp (measurable_snd.comp measurable_snd)))
  have hY : AEMeasurable (fun ω => (hcirc ω ε z - hcirc ω R 0, hcirc ω ε w - hcirc ω R 0,
      hcirc ω s w - hcirc ω ε w)) P :=
    (hh.hasLaw_recentred_circle hε hz).aemeasurable.prodMk
      ((hh.hasLaw_recentred_circle hε hw).aemeasurable.prodMk (hh.hasLaw_incr_le hs hsε w).aemeasurable)
  have h := GaussIndep.integral_mul_expWeight_eq_zero (hh.hasLaw_incr_le hs hsε z) hY
    (hh.indepFun_recentred_incr_of_le_le hs hsε hz hw hzw) hG γ
  refine Eq.trans ?_ h
  congr 1
  funext ω
  simp only [hGdef]
  ring

/-- Thin points, second moment: `E[T²] = ((ε/s)^{γ²} - 1) E[e^{2γ X}; X ≤ a]`, written with
`(ε/s)^{γ²} = e^{γ² log (ε/s)}`. -/
theorem integral_thin_sq_le_eq (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) {z : ℂ} (hz : ‖z‖ + ε ≤ R) (γ a : ℝ) :
    ∫ ω, ((Set.Iic a).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z)) ^ 2 ∂P =
      (∫ ω, (Set.Iic a).indicator (fun x => rexp (2 * γ * x)) (hcirc ω ε z - hcirc ω R 0) ∂P) *
        (rexp (γ ^ 2 * Real.log (ε / s)) - 1) := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hlog : ((Real.log (ε / s)).toNNReal : ℝ) = Real.log (ε / s) :=
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hs).mpr hsε))
  have hm : Measurable ((Set.Iic a).indicator fun x => rexp (γ * x)) :=
    (by fun_prop : Measurable fun x : ℝ => rexp (γ * x)).indicator measurableSet_Iic
  have h := GaussIndep.integral_mul_expWeight_sq (hh.hasLaw_incr_le hs hsε z)
    (hh.hasLaw_recentred_circle hε hz).aemeasurable (hh.indepFun_recentred_incr_le hs hsε hz) hm γ
  rw [hlog] at h
  rw [h]
  congr 2
  funext ω
  exact GaussTail.indicator_exp_mul_sq _ γ _

/-- Thin points, second-moment bound: for `α ≤ 2γ`,
`E[T²] ≤ ((ε/s)^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}` with `L = log (R / ε)` and the truncation `X ≤ α L`. -/
theorem integral_thin_sq_le_of_le (hh : IsWholePlaneGFF P hC hcirc) {s ε R : ℝ} (hs : 0 < s)
    (hsε : s ≤ ε) {z : ℂ} (hz : ‖z‖ + ε ≤ R) {γ α : ℝ} (hα : α ≤ 2 * γ) :
    ∫ ω, ((Set.Iic (α * Real.log (R / ε))).indicator (fun x => rexp (γ * x)) (hcirc ω ε z - hcirc ω R 0) *
        GaussIndep.expWeight γ (Real.log (ε / s)).toNNReal (hcirc ω s z - hcirc ω ε z)) ^ 2 ∂P ≤
      (rexp (γ ^ 2 * Real.log (ε / s)) - 1) * rexp (Real.log (R / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) := by
  have hε : 0 < ε := lt_of_lt_of_le hs hsε
  have hεR : ε ≤ R := by linarith [norm_nonneg z]
  have hL : ((Real.log (R / ε)).toNNReal : ℝ) = Real.log (R / ε) :=
    Real.coe_toNNReal _ (Real.log_nonneg ((one_le_div hε).mpr hεR))
  have hb := GaussTail.integral_indicator_Iic_exp_mul_le_of_hasLaw (hh.hasLaw_recentred_circle hε hz) hα
  rw [hL] at hb
  have hc : 0 ≤ rexp (γ ^ 2 * Real.log (ε / s)) - 1 := by
    have : 0 ≤ γ ^ 2 * Real.log (ε / s) :=
      mul_nonneg (sq_nonneg γ) (Real.log_nonneg ((one_le_div hs).mpr hsε))
    linarith [Real.add_one_le_exp (γ ^ 2 * Real.log (ε / s))]
  rw [hh.integral_thin_sq_le_eq hs hsε hz, mul_comm]
  refine mul_le_mul_of_nonneg_left (hb.trans (le_of_eq ?_)) hc
  congr 1
  ring

end IsWholePlaneGFF

end LatticeProb.Gauss

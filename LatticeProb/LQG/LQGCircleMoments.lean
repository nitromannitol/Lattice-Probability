import Mathlib
import LatticeProb.LQG.LQGCircleTail

/-!
# Exponential moments of circle averages of the whole-plane GFF

For circles inside the closed unit disc the covariance of two circle averages is
`-circlePairPotential`, so that

* `Var h_ε(x) = -log ε` (when `‖x‖ + ε ≤ 1`);
* `Cov(h_ε(x), h_ε(y)) = -log ‖x - y‖` when `2ε ≤ ‖x - y‖`, and
  `Cov(h_ε(x), h_ε(y)) ≤ log 2 - log ‖x - y‖` for all `x ≠ y`;
* the exponential moment of a finite linear combination of circle averages at a common scale is the
  Gaussian one, `E exp (∑ c_k h_ε(x_k)) = exp ((∑_k ∑_l c_k c_l Cov(h_ε(x_k), h_ε(x_l))) / 2)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.Gauss

/-- The circle average of `log max (‖·‖, 1)` over a circle inside the closed unit disc vanishes. -/
theorem circleAverage_logMaxAbs_eq_zero_of_add_le {z : ℂ} {r : ℝ} (hr : 0 < r) (h : ‖z‖ + r ≤ 1) :
    Real.circleAverage logMaxAbs z r = 0 := by
  have h0 : Real.circleAverage logMaxAbs z r = Real.circleAverage (fun _ : ℂ => (0 : ℝ)) z r := by
    refine Real.circleAverage_congr_sphere fun x hx => ?_
    have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
    have hxn : ‖x‖ ≤ 1 := by linarith [norm_le_insert' x z, norm_sub_rev x z]
    show Real.log (max ‖x‖ 1) = 0
    rw [max_eq_right hxn, Real.log_one]
  rw [h0, Real.circleAverage_const]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Covariance of two circle averages whose circles lie in the closed unit disc. -/
theorem IsWholePlaneGFF.covariance_circle_inside (hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) {z w : ℂ} (hz : ‖z‖ + r ≤ 1) (hw : ‖w‖ + s ≤ 1) :
    cov[fun ω => hcirc ω r z, fun ω => hcirc ω s w; P] = -circlePairPotential z r w s := by
  rw [hh.covariance_circle_circle hr hs, wholePlaneGFFCov_circle_circle_eq hs,
    circleAverage_logMaxAbs_eq_zero_of_add_le hr hz, circleAverage_logMaxAbs_eq_zero_of_add_le hs hw]
  ring

/-- `Var h_ε(x) = -log ε` for a circle inside the closed unit disc. -/
theorem IsWholePlaneGFF.variance_circle_inside (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : ‖x‖ + ε ≤ 1) :
    Var[fun ω => hcirc ω ε x; P] = -Real.log ε := by
  have hP := hh.isProbabilityMeasure
  rw [← covariance_self (hh.hasGaussianLaw_circle hε x).aemeasurable,
    hh.covariance_circle_inside hε hε hx hx, circlePairPotential_self_center hε.le, max_self]

/-- Circle averages at a common scale, with disjoint closed discs: the covariance is `-log ‖x - y‖`. -/
theorem IsWholePlaneGFF.covariance_circle_of_two_mul_le (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {x y : ℂ} (hx : ‖x‖ + ε ≤ 1) (hy : ‖y‖ + ε ≤ 1) (hxy : 2 * ε ≤ ‖x - y‖) :
    cov[fun ω => hcirc ω ε x, fun ω => hcirc ω ε y; P] = -Real.log ‖x - y‖ := by
  rw [hh.covariance_circle_inside hε hε hx hy, circlePairPotential_of_add_le hε hε.le (by linarith)]

/-- Circle averages at a common scale inside the closed unit disc:
`Cov(h_ε(x), h_ε(y)) ≤ log 2 - log ‖x - y‖` for `x ≠ y`. -/
theorem IsWholePlaneGFF.covariance_circle_le_log_two (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {x y : ℂ} (hx : ‖x‖ + ε ≤ 1) (hy : ‖y‖ + ε ≤ 1) (hxy : x ≠ y) :
    cov[fun ω => hcirc ω ε x, fun ω => hcirc ω ε y; P] ≤ Real.log 2 - Real.log ‖x - y‖ := by
  rw [hh.covariance_circle_inside hε hε hx hy]
  have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hc : Real.log (‖x - y‖ / 2) ≤ circlePairPotential x ε y ε := by
    have h := Real.circleAverage_mono (c := x) (R := ε)
      (f₁ := fun _ : ℂ => Real.log (‖x - y‖ / 2)) (f₂ := fun a => Real.log (max ε ‖a - y‖))
      (continuous_const.continuousOn.circleIntegrable')
      (continuous_log_max_norm_sub hε y).continuousOn.circleIntegrable' ?_
    · rwa [Real.circleAverage_const] at h
    · intro a ha
      have ha' : ‖a - x‖ = ε := (mem_sphere_iff_norm.1 ha).trans (abs_of_pos hε)
      show Real.log (‖x - y‖ / 2) ≤ Real.log (max ε ‖a - y‖)
      refine Real.log_le_log (by positivity) ?_
      by_cases h2 : ‖x - y‖ / 2 ≤ ε
      · exact h2.trans (le_max_left _ _)
      · have h3 := norm_sub_norm_le (x - y) (x - a)
        rw [sub_sub_sub_cancel_left, norm_sub_rev x a] at h3
        exact (by linarith : ‖x - y‖ / 2 ≤ ‖a - y‖).trans (le_max_right _ _)
  rw [Real.log_div hd.ne' two_ne_zero] at hc
  linarith

/-- The variance of a linear combination of circle averages at a common scale. -/
theorem IsWholePlaneGFF.variance_sum_circle (hh : IsWholePlaneGFF P hC hcirc) {A : ℕ} {ε : ℝ}
    (hε : 0 < ε) (x : Fin A → ℂ) (c : Fin A → ℝ) :
    Var[fun ω => ∑ k, c k * hcirc ω ε (x k); P] =
      ∑ k, ∑ l, c k * c l * cov[fun ω => hcirc ω ε (x k), fun ω => hcirc ω ε (x l); P] := by
  have hP := hh.isProbabilityMeasure
  let f : Fin A → GFFObservable.Admissible := fun k => ⟨.circle ε (x k), hε⟩
  have hproc := (hh.isGaussianProcess.comp_right f).smul c
  have hG : HasGaussianLaw (fun ω => ∑ k, c k * hcirc ω ε (x k)) P :=
    hproc.hasGaussianLaw_fun_sum (I := (Finset.univ : Finset (Fin A)))
  have hmem : ∀ k, MemLp (fun ω => c k * hcirc ω ε (x k)) 2 P := fun k =>
    (hh.memLp_two_circle hε (x k)).const_mul (c k)
  rw [← covariance_self hG.aemeasurable, covariance_fun_sum_fun_sum hmem hmem]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- **Law of a linear combination of circle averages at a common scale.** It is the centred Gaussian whose
variance is `∑_k ∑_l c_k c_l Cov(h_ε(x_k), h_ε(x_l))`. -/
theorem IsWholePlaneGFF.hasLaw_sum_circle (hh : IsWholePlaneGFF P hC hcirc) {A : ℕ} {ε : ℝ}
    (hε : 0 < ε) (x : Fin A → ℂ) (c : Fin A → ℝ) :
    HasLaw (fun ω => ∑ k, c k * hcirc ω ε (x k))
      (gaussianReal 0 (∑ k, ∑ l, c k * c l *
        cov[fun ω => hcirc ω ε (x k), fun ω => hcirc ω ε (x l); P]).toNNReal) P := by
  have hP := hh.isProbabilityMeasure
  let f : Fin A → GFFObservable.Admissible := fun k => ⟨.circle ε (x k), hε⟩
  have hproc := (hh.isGaussianProcess.comp_right f).smul c
  have hG : HasGaussianLaw (fun ω => ∑ k, c k * hcirc ω ε (x k)) P :=
    hproc.hasGaussianLaw_fun_sum (I := (Finset.univ : Finset (Fin A)))
  have hmem : ∀ k, MemLp (fun ω => c k * hcirc ω ε (x k)) 2 P := fun k =>
    (hh.memLp_two_circle hε (x k)).const_mul (c k)
  have hmean : ∫ ω, ∑ k, c k * hcirc ω ε (x k) ∂P = 0 := by
    rw [integral_finsetSum _ fun k _ => (hmem k).integrable (by norm_num)]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h0 : ∫ ω, hcirc ω ε (x k) ∂P = 0 := hh.integral_eq_zero (.circle ε (x k)) hε
    rw [integral_const_mul, h0, mul_zero]
  rw [← hh.variance_sum_circle hε x c]
  exact ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean]⟩

/-- The exponential of a linear combination of circle averages at a common scale is integrable. -/
theorem IsWholePlaneGFF.integrable_exp_sum_circle (hh : IsWholePlaneGFF P hC hcirc) {A : ℕ} {ε : ℝ}
    (hε : 0 < ε) (x : Fin A → ℂ) (c : Fin A → ℝ) :
    Integrable (fun ω => Real.exp (∑ k, c k * hcirc ω ε (x k))) P := by
  have hlaw := hh.hasLaw_sum_circle hε x c
  have h1 := integrable_exp_mul_gaussianReal (μ := 0)
    (v := (∑ k, ∑ l, c k * c l *
      cov[fun ω => hcirc ω ε (x k), fun ω => hcirc ω ε (x l); P]).toNNReal) 1
  rw [← hlaw.map_eq] at h1
  have h2 := (integrable_map_measure (by fun_prop) hlaw.aemeasurable).1 h1
  simpa [Function.comp_def] using h2

/-- **Gaussian exponential moment of circle averages at a common scale.**
`E exp (∑_k c_k h_ε(x_k)) = exp ((∑_k ∑_l c_k c_l Cov(h_ε(x_k), h_ε(x_l))) / 2)`. -/
theorem IsWholePlaneGFF.integral_exp_sum_circle (hh : IsWholePlaneGFF P hC hcirc) {A : ℕ} {ε : ℝ}
    (hε : 0 < ε) (x : Fin A → ℂ) (c : Fin A → ℝ) :
    ∫ ω, Real.exp (∑ k, c k * hcirc ω ε (x k)) ∂P =
      Real.exp ((∑ k, ∑ l, c k * c l *
        cov[fun ω => hcirc ω ε (x k), fun ω => hcirc ω ε (x l); P]) / 2) := by
  have hlaw := hh.hasLaw_sum_circle hε x c
  have hv0 : 0 ≤ ∑ k, ∑ l, c k * c l *
      cov[fun ω => hcirc ω ε (x k), fun ω => hcirc ω ε (x l); P] := by
    rw [← hh.variance_sum_circle hε x c]
    exact variance_nonneg _ _
  have hmgf := mgf_gaussianReal hlaw 1
  simp only [mgf, one_mul] at hmgf
  rw [hmgf, Real.coe_toNNReal _ hv0]
  norm_num

/-- **Mean one of the circle-average approximation density.** For `‖x‖ + ε ≤ 1`,
`E[ε^{γ²/2} e^{γ h_ε(x)}] = 1`. -/
theorem IsWholePlaneGFF.integral_rpow_mul_exp_circle (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : ‖x‖ + ε ≤ 1) (γ : ℝ) :
    ∫ ω, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε x) ∂P = 1 := by
  have h := hh.integral_exp_sum_circle hε (fun _ : Fin 1 => x) (fun _ => γ)
  have hcov : cov[fun ω => hcirc ω ε x, fun ω => hcirc ω ε x; P] = -Real.log ε := by
    rw [hh.covariance_circle_inside hε hε hx hx, circlePairPotential_self_center hε.le, max_self]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at h
  rw [integral_const_mul]
  have h' : ∫ ω, Real.exp (γ * hcirc ω ε x) ∂P = Real.exp (γ * γ * -Real.log ε / 2) := by
    rw [h, hcov]
  rw [h', Real.rpow_def_of_pos hε, ← Real.exp_add]
  rw [← Real.exp_zero]
  congr 1
  ring

end LatticeProb.Gauss

import LatticeProb.Gauss.GFFAffineInvariance
import LatticeProb.Gauss.CircleAverageApprox2
import LatticeProb.Gauss.UncorrelatedIndependence

/-!
# Covariances of circle averages of the whole-plane GFF, recentred at a large circle

Let `h` be a whole-plane GFF normalized so that its average over the unit circle vanishes, with circle averages
`h_r(z)`. Its covariance kernel `log (max(|x|,1) max(|y|,1) / |x - y|)` is not translation invariant, but the
recentred circle averages `h_r(z) - h_R(0)` of circles inside the disc `B_R(0)` have the covariance of the
Dirichlet-type kernel `log (R / |x - y|)`:

`Cov(h_r(z) - h_R(0), h_s(w) - h_R(0)) = log R - avg_{x ∈ ∂B_r(z)} log (max s |x - w|)`

whenever `|z| + r ≤ R` and `|w| + s ≤ R`. Consequences, in the form used for the second moment computation of
Gaussian multiplicative chaos (Duplantier-Sheffield): the variance of `h_r(z) - h_R(0)` is `log (R / r)`; the
increment `h_{r/2}(z) - h_r(z)` has law `N(0, log 2)`, is uncorrelated with `h_s(z) - h_R(0)` for `s ≥ r`, with
`h_s(w) - h_R(0)` for `r + s ≤ |z - w|`, and with the increment `h_{r/2}(w) - h_r(w)` for `2 r ≤ |z - w|`.

## Main statements

* `LatticeProb.Gauss.wholePlaneGFFCov_circle_circle_eq`, `LatticeProb.Gauss.wholePlaneGFFCov_recentred`
* `LatticeProb.Gauss.IsWholePlaneGFF.covariance_recentred_circle`, `variance_recentred_circle`,
  `hasLaw_recentred_circle`
* `LatticeProb.Gauss.IsWholePlaneGFF.covariance_increment_recentred` with its vanishing cases
  `covariance_increment_recentred_same_center`, `covariance_increment_recentred_of_add_le`
* `LatticeProb.Gauss.IsWholePlaneGFF.variance_increment`, `hasLaw_increment`,
  `covariance_increment_increment_of_le`
-/

open MeasureTheory ProbabilityTheory Metric
open LatticeProb.Gauss LatticeProb.LQG.AffineDerived

namespace LatticeProb.Gauss

/-! ### The potential of a circle averaged over another circle -/

/-- The logarithmic potential `x ↦ log (max s |x - w|)` of the uniform measure on `∂B_s(w)`, averaged over the
circle `∂B_r(z)`. -/
noncomputable def circlePairPotential (z : ℂ) (r : ℝ) (w : ℂ) (s : ℝ) : ℝ :=
  Real.circleAverage (fun x => Real.log (max s ‖x - w‖)) z r

theorem continuous_log_max_norm_sub {s : ℝ} (hs : 0 < s) (w : ℂ) :
    Continuous fun x : ℂ => Real.log (max s ‖x - w‖) :=
  (continuous_const.max (continuous_norm.comp (continuous_id.sub continuous_const))).log
    (fun _ => ne_of_gt (lt_of_lt_of_le hs (le_max_left _ _)))

/-- If the circle `∂B_r(z)` lies in the closed disc of radius `s` about `w`, the averaged potential is `log s`. -/
theorem circlePairPotential_of_le {z w : ℂ} {r s : ℝ} (h : ∀ x ∈ sphere z |r|, ‖x - w‖ ≤ s) :
    circlePairPotential z r w s = Real.log s := by
  unfold circlePairPotential
  exact Real.circleAverage_const_on_circle fun x hx => by rw [max_eq_left (h x hx)]

/-- If the circle `∂B_r(z)` lies outside the open disc of radius `s` about `w`, the averaged potential is
`log (max r |z - w|)`. -/
theorem circlePairPotential_of_ge {z w : ℂ} {r s : ℝ} (hr : 0 < r) (h : ∀ x ∈ sphere z |r|, s ≤ ‖x - w‖) :
    circlePairPotential z r w s = Real.log (max r ‖z - w‖) := by
  unfold circlePairPotential
  rw [← circleAverage_log_norm_sub_eq_log_max hr z w]
  refine Real.circleAverage_congr_sphere fun x hx => ?_
  show Real.log (max s ‖x - w‖) = Real.log ‖x - w‖
  rw [max_eq_right (h x hx)]

/-- Concentric circles: the averaged potential is `log (max s r)`. -/
theorem circlePairPotential_self_center {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    circlePairPotential z r z s = Real.log (max s r) := by
  unfold circlePairPotential
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_nonneg hr)
  rw [hx']

/-- Disjoint discs: the averaged potential is `log |z - w|`. -/
theorem circlePairPotential_of_add_le {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (h : r + s ≤ ‖z - w‖) :
    circlePairPotential z r w s = Real.log ‖z - w‖ := by
  rw [circlePairPotential_of_ge hr, max_eq_right (by linarith)]
  intro x hx
  have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
  have h1 := norm_sub_norm_le (z - w) (z - x)
  rw [sub_sub_sub_cancel_left, norm_sub_rev z x] at h1
  linarith

/-! ### The covariance kernel on pairs of circles -/

/-- The whole-plane covariance kernel averaged over two circles. -/
theorem wholePlaneGFFCov_circle_circle_eq {s : ℝ} (hs : 0 < s) (r : ℝ) (z w : ℂ) :
    wholePlaneGFFCov (.circle r z) (.circle s w) =
      Real.circleAverage logMaxAbs z r + Real.circleAverage logMaxAbs w s - circlePairPotential z r w s := by
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w s) z r = _
  have h1 : (fun x => Real.circleAverage (fun y => wholePlaneCov x y) w s) =
      fun x => (logMaxAbs x + Real.circleAverage logMaxAbs w s) - Real.log (max s ‖x - w‖) := by
    funext x
    exact circleAverage_wholePlaneCov hs
  have c1 : CircleIntegrable logMaxAbs z r := logMaxAbs_continuous.continuousOn.circleIntegrable'
  have c0 : CircleIntegrable (fun _ : ℂ => Real.circleAverage logMaxAbs w s) z r :=
    continuous_const.continuousOn.circleIntegrable'
  have c10 : CircleIntegrable (fun x : ℂ => logMaxAbs x + Real.circleAverage logMaxAbs w s) z r := c1.add c0
  have c2 : CircleIntegrable (fun x : ℂ => Real.log (max s ‖x - w‖)) z r :=
    (continuous_log_max_norm_sub hs w).continuousOn.circleIntegrable'
  rw [h1, Real.circleAverage_fun_sub c10 c2, Real.circleAverage_fun_add c1 c0, Real.circleAverage_const]
  rfl

/-- The kernel of the circle averages recentred at `∂B_R(0)`, for circles inside the closed disc `B_R(0)`: the
normalization terms cancel and `log R` minus the averaged potential remains. -/
theorem wholePlaneGFFCov_recentred {r s R : ℝ} (hr : 0 < r) (hs : 0 < s) {z w : ℂ} (hz : ‖z‖ + r ≤ R)
    (hw : ‖w‖ + s ≤ R) :
    wholePlaneGFFCov (.circle r z) (.circle s w) - wholePlaneGFFCov (.circle r z) (.circle R 0) -
        wholePlaneGFFCov (.circle R 0) (.circle s w) + wholePlaneGFFCov (.circle R 0) (.circle R 0) =
      Real.log R - circlePairPotential z r w s := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  have e1 : circlePairPotential z r 0 R = Real.log R := circlePairPotential_of_le fun x hx => by
    have hx' : ‖x - z‖ = r := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hr)
    have h1 := norm_sub_norm_le x z
    rw [sub_zero]
    linarith
  have e2 : circlePairPotential 0 R w s = Real.log R := by
    rw [circlePairPotential_of_ge hR, zero_sub, norm_neg, max_eq_left (by linarith)]
    intro x hx
    have hx' : ‖x‖ = R := (mem_sphere_zero_iff_norm.1 hx).trans (abs_of_pos hR)
    have h1 := norm_sub_norm_le x w
    linarith
  have e3 : circlePairPotential 0 R 0 R = Real.log R := by
    rw [circlePairPotential_self_center hR.le, max_self]
  rw [wholePlaneGFFCov_circle_circle_eq hs r z w, wholePlaneGFFCov_circle_circle_eq hR r z 0,
    wholePlaneGFFCov_circle_circle_eq hs R 0 w, wholePlaneGFFCov_circle_circle_eq hR R 0 0, e1, e2, e3]
  ring

/-! ### Covariances of recentred circle averages and of their dyadic increments -/

namespace IsWholePlaneGFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

theorem memLp_two_circle (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MemLp (fun ω => hcirc ω r z) 2 P :=
  (hh.hasGaussianLaw_circle hr z).memLp_two

theorem memLp_two_circle_sub (hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    MemLp (fun ω => hcirc ω r z - hcirc ω s w) 2 P :=
  (hh.memLp_two_circle hr z).sub (hh.memLp_two_circle hs w)

/-- The difference of two circle averages is a centered Gaussian random variable. -/
theorem hasGaussianLaw_circle_sub (hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (z w : ℂ) : HasGaussianLaw (fun ω => hcirc ω r z - hcirc ω s w) P :=
  hh.isGaussianProcess.hasGaussianLaw_fun_sub (s := (⟨.circle r z, hr⟩ : GFFObservable.Admissible))
    (t := (⟨.circle s w, hs⟩ : GFFObservable.Admissible))

theorem integral_circle_sub (hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    ∫ ω, (hcirc ω r z - hcirc ω s w) ∂P = 0 := by
  have h1 : ∫ ω, hcirc ω r z ∂P = 0 := hh.integral_eq_zero (.circle r z) hr
  have h2 : ∫ ω, hcirc ω s w ∂P = 0 := hh.integral_eq_zero (.circle s w) hs
  rw [integral_sub (hh.hasGaussianLaw_circle hr z).integrable (hh.hasGaussianLaw_circle hs w).integrable, h1, h2,
    sub_zero]

/-- The difference of two circle averages lies in the linear span of the Gaussian family of the field. -/
theorem circle_sub_mem_span (_hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    (fun ω => hcirc ω r z - hcirc ω s w) ∈ Submodule.span ℝ
      (Set.range fun (o : GFFObservable.Admissible) ω => o.1.eval (hC ω) (hcirc ω)) :=
  GaussIndep.fun_sub_mem_span_range (fun (o : GFFObservable.Admissible) ω => o.1.eval (hC ω) (hcirc ω))
    ⟨.circle r z, hr⟩ ⟨.circle s w, hs⟩

theorem covariance_circle_circle (hh : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (z w : ℂ) :
    cov[fun ω => hcirc ω r z, fun ω => hcirc ω s w; P] = wholePlaneGFFCov (.circle r z) (.circle s w) :=
  hh.covariance_eq (.circle r z) (.circle s w) hr hs

/-- Covariance of two circle averages recentred at `∂B_R(0)`, for circles inside the closed disc `B_R(0)`. -/
theorem covariance_recentred_circle (hh : IsWholePlaneGFF P hC hcirc) {r s R : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z w : ℂ} (hz : ‖z‖ + r ≤ R) (hw : ‖w‖ + s ≤ R) :
    cov[fun ω => hcirc ω r z - hcirc ω R 0, fun ω => hcirc ω s w - hcirc ω R 0; P] =
      Real.log R - circlePairPotential z r w s := by
  have hP := hh.isProbabilityMeasure
  have hR : 0 < R := by linarith [norm_nonneg z]
  have m1 := hh.memLp_two_circle hr z
  have m2 := hh.memLp_two_circle hs w
  have m0 := hh.memLp_two_circle hR 0
  have mZ := hh.memLp_two_circle_sub hs hR w 0
  rw [covariance_fun_sub_left m1 m0 mZ, covariance_fun_sub_right m1 m2 m0, covariance_fun_sub_right m0 m2 m0,
    hh.covariance_circle_circle hr hs, hh.covariance_circle_circle hr hR, hh.covariance_circle_circle hR hs,
    hh.covariance_circle_circle hR hR]
  have key := wholePlaneGFFCov_recentred hr hs hz hw
  linarith

/-- The variance of the circle average recentred at `∂B_R(0)` is `log (R / r)`. -/
theorem variance_recentred_circle (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ R) : Var[fun ω => hcirc ω r z - hcirc ω R 0; P] = Real.log (R / r) := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  rw [← covariance_self (hh.memLp_two_circle_sub hr hR z 0).aestronglyMeasurable.aemeasurable,
    hh.covariance_recentred_circle hr hr hz hz, circlePairPotential_self_center hr.le, max_self,
    Real.log_div hR.ne' hr.ne']

/-- The circle average recentred at `∂B_R(0)` has law `N(0, log (R / r))`. -/
theorem hasLaw_recentred_circle (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ R) :
    HasLaw (fun ω => hcirc ω r z - hcirc ω R 0) (gaussianReal 0 (Real.log (R / r)).toNNReal) P := by
  have hR : 0 < R := by linarith [norm_nonneg z]
  have hG := hh.hasGaussianLaw_circle_sub hr hR z 0
  exact ⟨hG.aemeasurable, by
    rw [hG.map_eq_gaussianReal, hh.integral_circle_sub hr hR, hh.variance_recentred_circle hr hz]⟩

/-- Covariance of a dyadic increment of circle averages with a recentred circle average. -/
theorem covariance_increment_recentred (hh : IsWholePlaneGFF P hC hcirc) {r s R : ℝ} (hr : 0 < r) (hs : 0 < s)
    {z w : ℂ} (hz : ‖z‖ + r ≤ R) (hw : ‖w‖ + s ≤ R) :
    cov[fun ω => hcirc ω (r / 2) z - hcirc ω r z, fun ω => hcirc ω s w - hcirc ω R 0; P] =
      circlePairPotential z r w s - circlePairPotential z (r / 2) w s := by
  have hP := hh.isProbabilityMeasure
  have hR : 0 < R := by linarith [norm_nonneg z]
  have hr2 : 0 < r / 2 := half_pos hr
  have hz2 : ‖z‖ + r / 2 ≤ R := by linarith
  have e : (fun ω => hcirc ω (r / 2) z - hcirc ω r z) =
      fun ω => (hcirc ω (r / 2) z - hcirc ω R 0) - (hcirc ω r z - hcirc ω R 0) := by
    funext ω
    ring
  rw [e, covariance_fun_sub_left (hh.memLp_two_circle_sub hr2 hR z 0) (hh.memLp_two_circle_sub hr hR z 0)
      (hh.memLp_two_circle_sub hs hR w 0),
    hh.covariance_recentred_circle hr2 hs hz2 hw, hh.covariance_recentred_circle hr hs hz hw]
  ring

/-- A dyadic increment at `z` is uncorrelated with the recentred circle averages at `z` of radius at least `r`. -/
theorem covariance_increment_recentred_same_center (hh : IsWholePlaneGFF P hC hcirc) {r s R : ℝ} (hr : 0 < r)
    (hrs : r ≤ s) {z : ℂ} (hz : ‖z‖ + s ≤ R) :
    cov[fun ω => hcirc ω (r / 2) z - hcirc ω r z, fun ω => hcirc ω s z - hcirc ω R 0; P] = 0 := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  rw [hh.covariance_increment_recentred hr hs (by linarith) hz, circlePairPotential_self_center hr.le,
    circlePairPotential_self_center (half_pos hr).le, max_eq_left hrs, max_eq_left (by linarith), sub_self]

/-- A dyadic increment at `z` is uncorrelated with the recentred circle averages over circles bounding discs
disjoint from `B_r(z)`. -/
theorem covariance_increment_recentred_of_add_le (hh : IsWholePlaneGFF P hC hcirc) {r s R : ℝ} (hr : 0 < r)
    (hs : 0 < s) {z w : ℂ} (hz : ‖z‖ + r ≤ R) (hw : ‖w‖ + s ≤ R) (hzw : r + s ≤ ‖z - w‖) :
    cov[fun ω => hcirc ω (r / 2) z - hcirc ω r z, fun ω => hcirc ω s w - hcirc ω R 0; P] = 0 := by
  rw [hh.covariance_increment_recentred hr hs hz hw, circlePairPotential_of_add_le hr hs.le hzw,
    circlePairPotential_of_add_le (half_pos hr) hs.le (by linarith), sub_self]

/-- The variance of a dyadic increment of circle averages is `log 2`. -/
theorem variance_increment (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Var[fun ω => hcirc ω (r / 2) z - hcirc ω r z; P] = Real.log 2 := by
  have hP := hh.isProbabilityMeasure
  have hr2 : 0 < r / 2 := half_pos hr
  have hR : 0 < ‖z‖ + r := by linarith [norm_nonneg z]
  have hz : ‖z‖ + r ≤ ‖z‖ + r := le_rfl
  have hz2 : ‖z‖ + r / 2 ≤ ‖z‖ + r := by linarith
  have mD := hh.memLp_two_circle_sub hr2 hr z z
  rw [← covariance_self mD.aestronglyMeasurable.aemeasurable]
  have e : (fun ω => hcirc ω (r / 2) z - hcirc ω r z) =
      fun ω => (hcirc ω (r / 2) z - hcirc ω (‖z‖ + r) 0) - (hcirc ω r z - hcirc ω (‖z‖ + r) 0) := by
    funext ω
    ring
  have step : cov[fun ω => hcirc ω (r / 2) z - hcirc ω r z,
      fun ω => (hcirc ω (r / 2) z - hcirc ω (‖z‖ + r) 0) - (hcirc ω r z - hcirc ω (‖z‖ + r) 0); P] =
      Real.log 2 := by
    rw [covariance_fun_sub_right mD (hh.memLp_two_circle_sub hr2 hR z 0) (hh.memLp_two_circle_sub hr hR z 0),
      hh.covariance_increment_recentred hr hr2 hz hz2, hh.covariance_increment_recentred hr hr hz hz,
      circlePairPotential_self_center hr.le, circlePairPotential_self_center hr2.le,
      circlePairPotential_self_center hr.le, circlePairPotential_self_center hr2.le, max_self, max_self,
      max_eq_right (by linarith : r / 2 ≤ r), max_eq_left (by linarith : r / 2 ≤ r),
      Real.log_div hr.ne' two_ne_zero]
    ring
  rw [← e] at step
  exact step

/-- A dyadic increment of circle averages has law `N(0, log 2)`. -/
theorem hasLaw_increment (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    HasLaw (fun ω => hcirc ω (r / 2) z - hcirc ω r z) (gaussianReal 0 (Real.log 2).toNNReal) P := by
  have hG := hh.hasGaussianLaw_circle_sub (half_pos hr) hr z z
  exact ⟨hG.aemeasurable, by
    rw [hG.map_eq_gaussianReal, hh.integral_circle_sub (half_pos hr) hr, hh.variance_increment hr]⟩

/-- Dyadic increments at the same scale `r` over discs `B_r(z)`, `B_r(w)` with disjoint interiors are
uncorrelated. -/
theorem covariance_increment_increment_of_le (hh : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) {z w : ℂ}
    (hzw : 2 * r ≤ ‖z - w‖) :
    cov[fun ω => hcirc ω (r / 2) z - hcirc ω r z, fun ω => hcirc ω (r / 2) w - hcirc ω r w; P] = 0 := by
  have hP := hh.isProbabilityMeasure
  have hr2 : 0 < r / 2 := half_pos hr
  set R : ℝ := max ‖z‖ ‖w‖ + r with hRdef
  have hR : 0 < R := by
    have := le_max_left ‖z‖ ‖w‖
    linarith [norm_nonneg z]
  have hz : ‖z‖ + r ≤ R := by
    have := le_max_left ‖z‖ ‖w‖
    linarith
  have hw : ‖w‖ + r ≤ R := by
    have := le_max_right ‖z‖ ‖w‖
    linarith
  have hw2 : ‖w‖ + r / 2 ≤ R := by linarith
  have e : (fun ω => hcirc ω (r / 2) w - hcirc ω r w) =
      fun ω => (hcirc ω (r / 2) w - hcirc ω R 0) - (hcirc ω r w - hcirc ω R 0) := by
    funext ω
    ring
  rw [e, covariance_fun_sub_right (hh.memLp_two_circle_sub hr2 hr z z) (hh.memLp_two_circle_sub hr2 hR w 0)
      (hh.memLp_two_circle_sub hr hR w 0),
    hh.covariance_increment_recentred_of_add_le hr hr2 hz hw2 (by linarith),
    hh.covariance_increment_recentred_of_add_le hr hr hz hw (by linarith), sub_self]

end IsWholePlaneGFF

end LatticeProb.Gauss

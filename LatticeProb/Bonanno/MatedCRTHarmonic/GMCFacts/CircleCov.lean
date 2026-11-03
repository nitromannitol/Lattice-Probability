/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.CircleCov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-!
# Covariances of the recentred circle-average process

For the circle-average process `H r z = h_r(z)` of a whole-plane GFF normalized by `h_1(0) = 0`
(`LQGDimension.IsGFFCircleAverage`), the increments `h_r(w) − h_ε(z)` measured from a fixed circle `∂B_ε(z)` are
log-correlated **uniformly in `z` and `ε`**: for `w, w' ∈ B̄_{ε/2}(z)` and `0 < r ≤ ε/2`,

  `|Cov(h_r(w) − h_ε(z), h_r(w') − h_ε(z)) + log max(r, |w − w'|) − log ε| ≤ log 2`

(`abs_cov_recentred_add_log_sub_log_le`). This is the covariance computation behind the coordinate change (3.15)–(3.16)
of [GHM15, Lemma 3.12] (: the field `h(ε · + z) − h_ε(z)` has the law of
a normalized whole-plane GFF), in the quantitative form needed for a Kahane comparison: no field-level coordinate change
is used. Ingredients: LQGMetric's identity `gffCircleCov = incCov` (`CircleAvg.gffCircleCov_eq_incCov`) and Newton's
theorem `circLog w r x = log max(r, |w − x|)` (`CircleAvg.circLog_eq_log_max`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric.CircleAvg

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-! ### Newton's theorem for the circle covariances `circCov` -/

/-- `circCov z r z r = log r`. -/
lemma circCov_self {r : ℝ} (hr : 0 < r) (z : ℂ) : circCov z r z r = Real.log r := by
  rw [circCov_center z hr r hr, inv_mul_cancel₀ hr.ne', Real.posLog_one, add_zero]

/-- A circle `∂B_r(w)` inside `B̄_ε(z)`: `circCov w r z ε = log ε`. -/
lemma circCov_of_inside {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {w z : ℂ} (h : ‖w - z‖ + r ≤ ε) :
    circCov w r z ε = Real.log ε := by
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  rw [mem_sphere_iff_norm, abs_of_pos hr] at hx
  rw [circLog_eq_log_max hε, max_eq_left]
  calc ‖z - x‖ = ‖(w - x) - (w - z)‖ := by congr 1; abel
    _ ≤ ‖w - x‖ + ‖w - z‖ := norm_sub_le _ _
    _ = r + ‖w - z‖ := by rw [norm_sub_rev, hx]
    _ ≤ ε := by linarith

/-- A small circle `∂B_r(w)` with `w ∈ B̄_{ε/2}(z)`, `r ≤ ε/2`, seen from `∂B_ε(z)`: `circCov z ε w r = log ε`. -/
lemma circCov_of_outside {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hrε : r ≤ ε / 2) {w z : ℂ}
    (h : ‖w - z‖ ≤ ε / 2) : circCov z ε w r = Real.log ε := by
  have e : circCov z ε w r = circLog z ε w := by
    refine Real.circleAverage_congr_sphere fun x hx => ?_
    rw [mem_sphere_iff_norm, abs_of_pos hε] at hx
    have hwx : r ≤ ‖w - x‖ := by
      have : ‖x - z‖ ≤ ‖w - x‖ + ‖w - z‖ := by
        calc ‖x - z‖ = ‖(w - z) - (w - x)‖ := by congr 1; abel
          _ ≤ ‖w - z‖ + ‖w - x‖ := norm_sub_le _ _
          _ = ‖w - x‖ + ‖w - z‖ := add_comm _ _
      linarith
    rw [circLog_eq_log_max hr, max_eq_right hwx, norm_sub_rev]
  rw [e, circLog_eq_log_max hε, max_eq_left (by rw [norm_sub_rev]; linarith)]

/-- Two circles of the same radius: `log max(r, |w − w'|) ≤ circCov w r w' r ≤ log max(r, |w − w'|) + log 2`. -/
lemma circCov_same_radius_bounds {r : ℝ} (hr : 0 < r) (w w' : ℂ) :
    Real.log (max r ‖w - w'‖) ≤ circCov w r w' r ∧
      circCov w r w' r ≤ Real.log (max r ‖w - w'‖) + Real.log 2 := by
  have hci : CircleIntegrable (circLog w' r) w r :=
    (continuous_circLog hr.ne' w').continuousOn.circleIntegrable'
  have hM : 0 < max r ‖w - w'‖ := lt_max_of_lt_left hr
  constructor
  · rcases le_or_gt ‖w - w'‖ r with hle | hlt
    · rw [max_eq_left hle]
      calc Real.log r = Real.circleAverage (fun _ => Real.log r) w r :=
            (Real.circleAverage_const _ w r).symm
        _ ≤ circCov w r w' r := by
          refine Real.circleAverage_mono (circleIntegrable_const _ _ _) hci fun x _ => ?_
          rw [circLog_eq_log_max hr]
          exact Real.log_le_log hr (le_max_left _ _)
    · -- `w'` lies outside `B̄_r(w)`: compare with `log |x − w'|`, whose circle average is `circLog w r w'`
      have hci' : CircleIntegrable (fun x => Real.log ‖x - w'‖) w r :=
        circleIntegrable_log_norm_sub_const r
      calc Real.log (max r ‖w - w'‖) = circLog w r w' := (circLog_eq_log_max hr w w').symm
        _ = Real.circleAverage (fun x => Real.log ‖x - w'‖) w r := rfl
        _ ≤ circCov w r w' r := by
          refine Real.circleAverage_mono hci' hci fun x hx => ?_
          rw [mem_sphere_iff_norm, abs_of_pos hr] at hx
          have hpos : 0 < ‖x - w'‖ := by
            have : ‖w - w'‖ ≤ ‖x - w'‖ + ‖x - w‖ := by
              calc ‖w - w'‖ = ‖(x - w') - (x - w)‖ := by congr 1; abel
                _ ≤ ‖x - w'‖ + ‖x - w‖ := norm_sub_le _ _
            linarith
          show Real.log ‖x - w'‖ ≤ circLog w' r x
          rw [circLog_eq_log_max hr, norm_sub_rev w' x]
          exact Real.log_le_log hpos (le_max_right _ _)
  · refine Real.circleAverage_mono_on_of_le_circle hci fun x hx => ?_
    rw [mem_sphere_iff_norm, abs_of_pos hr] at hx
    rw [circLog_eq_log_max hr, add_comm, ← Real.log_mul two_ne_zero hM.ne']
    refine Real.log_le_log (lt_max_of_lt_left hr) (max_le ?_ ?_)
    · nlinarith [le_max_left r ‖w - w'‖]
    · calc ‖w' - x‖ = ‖(x - w) - (w' - w)‖ := by rw [norm_sub_rev]; congr 1; abel
        _ ≤ ‖x - w‖ + ‖w' - w‖ := norm_sub_le _ _
        _ = r + ‖w - w'‖ := by rw [hx, norm_sub_rev]
        _ ≤ 2 * max r ‖w - w'‖ := by
          nlinarith [le_max_left r ‖w - w'‖, le_max_right r ‖w - w'‖]

/-! ### The recentred process -/

/-- `gffCircleCov` through LQGMetric's `circCov` (`CircleAvg.gffCircleCov_eq_incCov`). -/
lemma gffCircleCov_eq_circCov {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (z w : ℂ) :
    LQGDimension.gffCircleCov ε z δ w =
      -circCov z ε w δ + circCov z ε 0 1 + circCov 0 1 w δ - circCov 0 1 0 1 := by
  rw [gffCircleCov_eq_incCov hε hδ]
  rfl

/-- Each circle average is square integrable (it is Gaussian). -/
lemma memLp_two_coord (hH : LQGDimension.IsGFFCircleAverage H P) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MemLp (H r z) 2 P :=
  (hH.isGaussianProcess.hasGaussianLaw_eval (⟨r, hr⟩, z)).memLp_two

/-- The covariance of two increments measured from the same circle `∂B_ε(z)`; the normalization terms (circle
`∂𝔻`) cancel. -/
theorem cov_recentred (hH : LQGDimension.IsGFFCircleAverage H P) {ε r r' : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (hr' : 0 < r') (z w w' : ℂ) :
    cov[fun ω => H r w ω - H ε z ω, fun ω => H r' w' ω - H ε z ω; P] =
      -circCov w r w' r' + circCov w r z ε + circCov z ε w' r' - circCov z ε z ε := by
  have := hH.isProbabilityMeasure
  have hA := memLp_two_coord hH hr w
  have hB := memLp_two_coord hH hr' w'
  have hC := memLp_two_coord hH hε z
  change cov[H r w - H ε z, H r' w' - H ε z; P] = _
  rw [covariance_sub_sub hA hC hB hC, hH.covariance_eq r hr r' hr' w w',
    hH.covariance_eq r hr ε hε w z, hH.covariance_eq ε hε r' hr' z w',
    hH.covariance_eq ε hε ε hε z z, gffCircleCov_eq_circCov hr hr', gffCircleCov_eq_circCov hr hε,
    gffCircleCov_eq_circCov hε hr', gffCircleCov_eq_circCov hε hε]
  ring

/-- **Uniform log-correlation of the recentred process**: for `w, w' ∈ B̄_{ε/2}(z)` and `0 < r ≤ ε/2`,
`|Cov(h_r(w) − h_ε(z), h_r(w') − h_ε(z)) + log max(r, |w − w'|) − log ε| ≤ log 2`. -/
theorem abs_cov_recentred_add_log_sub_log_le (hH : LQGDimension.IsGFFCircleAverage H P)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε / 2) {z w w' : ℂ} (hw : ‖w - z‖ ≤ ε / 2)
    (hw' : ‖w' - z‖ ≤ ε / 2) :
    |cov[fun ω => H r w ω - H ε z ω, fun ω => H r w' ω - H ε z ω; P] +
        Real.log (max r ‖w - w'‖) - Real.log ε| ≤ Real.log 2 := by
  rw [cov_recentred hH hε hr hr z w w', circCov_of_inside hr hε (by linarith),
    circCov_of_outside hr hε hrε hw', circCov_self hε]
  obtain ⟨h1, h2⟩ := circCov_same_radius_bounds hr w w'
  rw [abs_le]
  constructor <;> linarith

/-- The variance of the recentred circle average: `Var(h_r(w) − h_ε(z)) = log ε − log r` for `w ∈ B̄_{ε/2}(z)` and
`0 < r ≤ ε/2`. -/
theorem cov_recentred_self (hH : LQGDimension.IsGFFCircleAverage H P) {ε r : ℝ} (hε : 0 < ε)
    (hr : 0 < r) (hrε : r ≤ ε / 2) {z w : ℂ} (hw : ‖w - z‖ ≤ ε / 2) :
    cov[fun ω => H r w ω - H ε z ω, fun ω => H r w ω - H ε z ω; P] =
      Real.log ε - Real.log r := by
  rw [cov_recentred hH hε hr hr z w w, circCov_of_inside hr hε (by linarith),
    circCov_of_outside hr hε hrε hw, circCov_self hε, circCov_self hr]
  ring

end MatedCRTHarmonic.GMCFacts

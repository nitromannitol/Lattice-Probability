/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.Gaussian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Defs
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import Mathlib.Probability.ConditionalProbability

/-!
# The law of the Case 3 index and the small-root conditional law

Source: (`[18]:N`), Proposition 4.10, Cases 2–3,
`[18]`.

* `incCov_offCenter`: for `B̄_r(z₀) ⊆ B̄_1(0)` (`‖z₀‖ + r ≤ 1`), the covariance of the increment
  `h_r(z₀) − h_1(0)` of a whole-plane GFF is `−log r` (Newton's theorem on both circles);
* `map_radAvg_normalized`: for a whole-plane GFF normalized by `h_1(0) = 0`, the circle average
  `h_r(z₀)` is centred Gaussian with variance `log(1/r)` — the same law for every root `z₀` with
  `B̄_r(z₀) ⊆ B̄_1(0)`. With `h² = h − γ log|· − z₀|` the Case 3 index `h²_r(z₀) = h_r(z₀) + γ log(1/r)`
  therefore has law `N(γ log(1/r), log(1/r))`, which is exactly the law of the γ-cone's circle average
  `h^{cone}_r(0) = B_{log(1/r)} + γ log(1/r)` (the coherence used by the repaired Case 3);
* `prod_cond_univ_prod`: conditioning a product law on `univ ×ˢ s` conditions the second factor
  (the Case 2 conditional law `(P ⊗ λ)[· | z ∈ B_ρ]` is `P ⊗ λ[· | B_ρ]`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.CircleAvg

/-- `Var(h_r(z₀) − h_1(0)) = −log r` when `‖z₀‖ + r ≤ 1`. -/
theorem incCov_offCenter {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z₀‖ + r ≤ 1) :
    incCov z₀ r 0 1 z₀ r 0 1 = -Real.log r := by
  have hr1 : r ≤ 1 := by linarith [norm_nonneg z₀]
  have h1 : circCov z₀ r z₀ r = Real.log r := by
    rw [circCov_center z₀ hr r hr, inv_mul_cancel₀ hr.ne']
    simp [Real.posLog]
  have h2 : circCov z₀ r 0 1 = 0 := by
    refine Real.circleAverage_const_on_circle fun x hx => ?_
    rw [circLog_eq one_ne_zero, Real.log_one, zero_add, inv_one, one_mul]
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (norm_nonneg _)]
    rw [mem_sphere_iff_norm, abs_of_pos hr] at hx
    calc ‖(0 : ℂ) - x‖ = ‖x‖ := by rw [zero_sub, norm_neg]
      _ = ‖(x - z₀) + z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ 1 := by rw [hx]; linarith
  have h3 : circCov 0 1 z₀ r = 0 := by
    have e : circCov 0 1 z₀ r = circLog 0 1 z₀ := by
      show Real.circleAverage (circLog z₀ r) 0 1 =
        Real.circleAverage (fun a => Real.log ‖a - z₀‖) 0 1
      refine Real.circleAverage_congr_sphere fun u hu => ?_
      rw [mem_sphere_iff_norm, abs_one, sub_zero] at hu
      rw [circLog_eq hr.ne']
      have hdist : r ≤ ‖z₀ - u‖ := by
        have := norm_sub_norm_le u z₀
        rw [hu, norm_sub_rev] at this
        linarith
      have hge : 1 ≤ r⁻¹ * ‖z₀ - u‖ := by
        rw [le_inv_mul_iff₀ hr, mul_one]
        exact hdist
      have hpos : 0 < ‖z₀ - u‖ := lt_of_lt_of_le hr hdist
      rw [Real.posLog_eq_log (by rwa [abs_of_nonneg (by positivity)]), Real.log_mul (inv_ne_zero hr.ne') hpos.ne',
        Real.log_inv, norm_sub_rev]
      ring
    rw [e, circLog_eq one_ne_zero, Real.log_one, zero_add, inv_one, one_mul,
      Real.posLog_eq_zero_iff, abs_of_nonneg (norm_nonneg _), zero_sub, norm_neg]
    linarith
  have h4 : circCov 0 1 0 1 = 0 := by
    rw [circCov_center 0 one_pos 1 one_pos]
    simp [Real.posLog]
  rw [incCov, h1, h2, h3, h4]
  ring

/-- **The law of the Case 3 index.** For a whole-plane GFF normalized by `h_1(0) = 0` and
`‖z₀‖ + r ≤ 1`, `h_r(z₀)` is centred Gaussian with variance `log(1/r)`. -/
theorem map_radAvg_normalized {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) {z₀ : ℂ} (hz : ‖z₀‖ + r ≤ 1) :
    P.map (fun ω => radAvg r (h ω) z₀) = gaussianReal 0 (-Real.log r).toNNReal := by
  have hcongr : (fun ω => radAvg r (h ω) z₀) =ᵐ[P] cInc h r z₀ 1 0 := by
    filter_upwards [hh.2] with ω hω
    simp only [radAvg, cInc, hω, sub_zero]
  rw [Measure.map_congr hcongr, (map_cInc hh.1 hr one_pos z₀ 0).1, incCov_offCenter hr hz]

/-! ## The small-root conditional law -/

/-- Conditioning a product law on `univ ×ˢ s` conditions the second factor. -/
theorem prod_cond_univ_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν] (s : Set β) :
    (μ.prod ν)[|univ ×ˢ s] = μ.prod (ν[|s]) := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.prod_prod, measure_univ, one_mul,
    ← Measure.prod_restrict, Measure.restrict_univ, Measure.prod_smul_right]

end MatedCRTHarmonic.GMSCase

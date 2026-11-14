/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianNestedConfinement at commit fdb5cad; local import paths and an additional prerequisite import are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNestedClock
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianNestedSurvival
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRangeComparison
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRangeComparisonExtra

/-! The finite nested-excursion survival estimate controls the whole actual
outer-stopped path. The proof compares the original path's exit times. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

theorem brownian_outer_exit_range_bad_le_of_step {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ] (hμ : IsStandardBrownianLaw μ)
    (U : Set (Euc d)) (hUb : Bornology.IsBounded U) (p : Euc d)
    {r R : ℝ} (hr : 0 < r) (hR : 1 < R) {x : Euc d} (hx : dist x p ≤ r)
    (δ : ℝ) (hstart : x ∈ thickening δ U) (N : ℕ) (hN : 0 < N)
    (η : ℝ) (hη : R * (r * R ^ (N - 1)) + dist x p ≤ η)
    (q : ℝ≥0∞)
    (hstep : ∀ i < N, ∀ y : Euc d, dist y p ≤ r * R ^ i →
      brownianExcursionKernel (U := nestedBrownianBall p r R i) isOpen_ball μ y
        (curveRangeEvent (cthickening δ U)) ≤ q) :
    μ {ω | stoppedBrownianRepresentative (thickening δ U) x ω ∉
      curveRangeEvent (closedBall x η)} ≤ q ^ N := by
  let V := nestedBrownianBall p r R
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hmono : Monotone V := by
    intro i j hij
    exact ball_subset_ball (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR.le hij) hr.le) hRpos.le)
  have hxV : x ∈ V (N - 1) := by
    change dist x p < R * (r * R ^ (N - 1))
    have hbase : r ≤ r * R ^ (N - 1) :=
      le_mul_of_one_le_right hr.le (one_le_pow₀ hR.le)
    have hpos : 0 < r * R ^ (N - 1) := mul_pos hr (pow_pos hRpos _)
    exact hx.trans_lt (hbase.trans_lt (by nlinarith))
  have hsub : {ω | stoppedBrownianRepresentative (thickening δ U) x ω ∉
      curveRangeEvent (closedBall x η)} ≤ᵐ[μ]
      {ω | ∀ i < N, (brownianSkeletonExcursion V x 0
        (fun n _ => some n) i ω).2 ∈ curveRangeEvent (cthickening δ U)} := by
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
      standardBrownianLaw_ae_finiteExit hd hμ
        (show Bornology.IsBounded (V (N - 1)) from isBounded_ball) x,
      standardBrownianLaw_ae_finiteExit hd hμ
        (show Bornology.IsBounded (thickening δ U) from hUb.thickening) x]
      with ω hzero hfinite houter
    intro hbad
    have hstartV : x + ω 0 ∈ V (N - 1) := by simpa only [hzero, add_zero] using hxV
    have hstartOuter : x + ω 0 ∈ thickening δ U := by
      simpa only [hzero, add_zero] using hstart
    have hexit : continuousExitTime (V (N - 1)) x ω ≤
        continuousExitTime (thickening δ U) x ω := by
      by_contra hn
      have hle := (lt_of_not_ge hn).le
      apply hbad
      intro u
      exact (stoppedBrownianRepresentative_dist_le_of_exit_le
        (thickening δ U) p x (R * (r * R ^ (N - 1))) ω
        hstartV hfinite hle u).trans hη
    have hstay : ∀ t : ℝ≥0, t ≤ (continuousExitTime (V (N - 1)) x ω).toNNReal →
        x + ω t ∈ cthickening δ U := by
      intro t ht
      apply mem_cthickening_of_le_outerExit U δ hstartOuter houter
      apply le_trans _ hexit
      simpa only [ENNReal.coe_toNNReal hfinite] using ENNReal.coe_le_coe.mpr ht
    intro i hi u
    exact brownianSkeletonExcursion_nested_range_subset V hmono (cthickening δ U)
      x ω (N - 1) hfinite hstay i (by omega) ⟨u, rfl⟩
  exact (measure_mono_ae hsub).trans
    (brownian_nested_survival_le_of_step hd μ hμ p hr hR hx isClosed_cthickening q N hstep)

end BouRabeeGwynne

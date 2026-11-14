/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossQuantileWindow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SquareCrossPercConcrete
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BTight

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem square_cross_quantile_window_of_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : ℝ) (n : ℕ)
    (p T : ℝ) (hp : 0 < p) (hp1 : p < 1) (hT : 0 < T)
    (hlo : P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω <
      T⁻¹ * lambdaN ξ W P n} < ENNReal.ofReal p)
    (hhi : P {ω | T * lambdaN ξ W P n <
      lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω} < ENNReal.ofReal p) :
    T⁻¹ * lambdaN ξ W P n ≤ ellN ξ W P n (ENNReal.ofReal p) ∧
      ellBarN ξ W P n (ENNReal.ofReal p) ≤ T * lambdaN ξ W P n := by
  let q : ℝ≥0∞ := ENNReal.ofReal p
  have hq0 : 0 < q := ENNReal.ofReal_pos.2 hp
  have hq1 : q < 1 := by
    simpa only [q] using (ENNReal.ofReal_lt_one.mpr hp1)
  have hv := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hmeas : Measurable (lenObs ξ (phiMN W P 0 n) (rectAB 1 1)) :=
    measurable_lenObs hv.cont hv.meas _
  constructor
  · by_contra hn
    have hlt : ellN ξ W P n q < T⁻¹ * lambdaN ξ W P n := lt_of_not_ge hn
    have hprob : q ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
        ellN ξ W P n q} := prob_le_ellQ hv.cont hv.meas _ hq0 hq1
    have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω ≤
        ellN ξ W P n q} ⊆
        {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω <
          T⁻¹ * lambdaN ξ W P n} := by
      intro ω hω
      exact lt_of_le_of_lt hω hlt
    exact (not_le_of_gt hlo) (hprob.trans (measure_mono hsub))
  · by_contra hn
    have hlt : T * lambdaN ξ W P n < ellBarN ξ W P n q := lt_of_not_ge hn
    have hqbar0 : 0 < 1 - q := tsub_pos_iff_lt.mpr hq1
    have hqbar1 : 1 - q < 1 := by
      exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne'
    have hprob : 1 - (1 - q) ≤
        P {ω | ellBarN ξ W P n q ≤
          lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω} :=
      prob_ge_ellQ hv.cont hv.meas _ hqbar0 hqbar1
    have hsub : {ω | ellBarN ξ W P n q ≤
        lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω} ⊆
        {ω | T * lambdaN ξ W P n <
          lenObs ξ (phiMN W P 0 n) (rectAB 1 1) ω} := by
      intro ω hω
      exact lt_of_lt_of_le hlt hω
    have hqeq : 1 - (1 - q) = q :=
      ENNReal.sub_sub_cancel ENNReal.one_ne_top hq1.le
    rw [hqeq] at hprob
    exact (not_le_of_gt hhi) (hprob.trans (measure_mono hsub))

end SupercriticalLQGUniqueness.B2.DG20Pt

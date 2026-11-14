/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicMedianCompare
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P10Law
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Bridge

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem map_lenObs_phiVer_eq_of_whiteNoise
    {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂}
    {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V)
    (ξ δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    P.map (lenObs ξ (phiVer W P δ 1) (rectAB 1 1)) =
      P₂.map (lenObs ξ (phiVer V P₂ δ 1) (rectAB 1 1)) := by
  have hv := isPhiVersion_phiVer hW hδ hδ1
  have hv₂ := isPhiVersion_phiVer hV hδ hδ1
  have hm := measurable_lenObs hv.cont hv.meas (rectAB 1 1) (ξ := ξ)
  have hm₂ := measurable_lenObs hv₂.cont hv₂.meas (rectAB 1 1) (ξ := ξ)
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hm hS, Measure.map_apply hm₂ hS]
  have hS' : MeasurableSet {x : ℝ≥0∞ | x.toReal ∈ S} :=
    hS.preimage ENNReal.measurable_toReal
  have he := measure_crossLenIn_phiVer_eq
    (ξ := ξ) (K := (rectAB 1 1).toSet)
    (A := (rectAB 1 1).side₁) (B := (rectAB 1 1).side₂)
    (rectAB 1 1).isCompact_toSet hW hV hδ hδ1 hS'
  change
    P {ω | (rectLen ξ (fun z => phiVer W P δ 1 z ω)
      (rectAB 1 1)).toReal ∈ S} =
    P₂ {ω | (rectLen ξ (fun z => phiVer V P₂ δ 1 z ω)
      (rectAB 1 1)).toReal ∈ S}
  simpa only [rectLen, Set.mem_setOf_eq] using he

 
theorem lambdaDelta_eq_of_whiteNoise
    {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂}
    {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V)
    (ξ δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    lambdaDelta ξ W P δ = lambdaDelta ξ V P₂ δ := by
  unfold lambdaDelta
  exact congrArg lowerMedianLaw
    (map_lenObs_phiVer_eq_of_whiteNoise hW hV ξ δ hδ hδ1)

end SupercriticalLQGUniqueness.B2.DG20Pt

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicPointWNLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistOpenLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffLaw2

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_measure_lfppDOn_phiVer_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (W : WNSpace → Ω → ℝ) (W' : WNSpace → Ω' → ℝ)
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W')
    (ξ : ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (U : Set ℂ) (hU : IsOpen U) (z w : ℂ)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | lfppDOn ξ (fun x => phiVer W P a b x ω) U z w ∈ S} =
      P' {ω | lfppDOn ξ (fun x => phiVer W' P' a b x ω) U z w ∈ S} := by
  have hφ := isPhiVersion_phiVer hW ha hab
  have hφ' := isPhiVersion_phiVer hW' ha hab
  exact dg20_measure_lfppDOn_open_eq
    hφ.cont hφ.meas hφ'.cont hφ'.meas
    (map_phi_eq hW hW' a b hφ.meas hφ'.meas hφ.ae_eq hφ'.ae_eq)
    ξ U hU z w hS

end SupercriticalLQGUniqueness.B2.DG20Pt

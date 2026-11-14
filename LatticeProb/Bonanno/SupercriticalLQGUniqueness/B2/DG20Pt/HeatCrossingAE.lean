/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingAE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatCrossingMeasurable
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable

 

set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_aemeasurable_heat_crossing
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ε : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h ε X) (ξ : ℝ) :
    AEMeasurable (fun ω => lfppCrossingLength ξ (X ω)) P :=
  (dg20_measurable_lfppCrossingLength ξ).comp_aemeasurable
    (B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh ε X hX)

end SupercriticalLQGUniqueness.B2.DG20Pt

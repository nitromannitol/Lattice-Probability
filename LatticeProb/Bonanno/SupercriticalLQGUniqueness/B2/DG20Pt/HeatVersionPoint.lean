/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPhiCrossingComparison
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.HeatVersion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_heat_smoothing_ae_heatMollify
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ε : Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h ε X) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, X ω z = heatMollify (ε : ℝ) (h ω) z := by
  obtain ⟨H, hHeq, hHlim⟩ := exists_heatVersion hh (ε : ℝ) ε.2
  have hXY := Exponent.HeatVersion.ae_eq_continuous_heat_versions
    (ε : ℝ) ε.2 X H hX hHlim
  filter_upwards [hXY, hHeq] with ω heq hHω
  intro z
  rw [heq]
  exact hHω z

end SupercriticalLQGUniqueness.B2.DG20Pt

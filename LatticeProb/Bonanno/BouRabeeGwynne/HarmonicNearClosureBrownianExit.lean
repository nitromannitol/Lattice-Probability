/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.HarmonicNearClosureBrownianExit at commit fdb5cad. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianHarmonicExit

/-! The stopped Brownian endpoint law is carried by the domain boundary. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace BouRabeeGwynne

/-- The actual stopped-curve endpoint law is carried by the domain boundary. -/
theorem standardBrownianLaw_stopped_endPoint_ae_mem_frontier {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : Euc d} (hz : z ∈ U) :
    ∀ᵐ x ∂((stoppedBrownianLaw U z μ).map CurveSpace.endPoint), x ∈ frontier U := by
  rw [stoppedBrownianLaw, Measure.map_map CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedBrownianCurve hU z)]
  apply (ae_map_iff (CurveSpace.continuous_endPoint.measurable.comp
    (measurable_stoppedBrownianCurve hU z)).aemeasurable
    isClosed_frontier.measurableSet).mpr
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ,
    standardBrownianLaw_ae_finiteExit hd hμ hUb z] with ω hzero hfinite
  apply stoppedBrownianCurve_endPoint_mem_frontier hU _ hfinite
  simpa only [hzero, add_zero] using hz

end BouRabeeGwynne

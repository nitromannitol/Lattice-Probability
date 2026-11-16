import LatticeProb.MeasureTheory.ProfileIntegralPseudoMetric
import LatticeProb.MeasureTheory.TruncatedDistanceConvergence
import LatticeProb.MeasureTheory.TruncatedDistanceConverse

/-! # Convergence in the integrated profile pseudometric -/

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal Topology

namespace LatticeProb.MeasurableProfile

variable {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
  (μ : Measure α) [IsFiniteMeasure μ]

/-- Pseudometric convergence of profiles implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto {ι : Type*} {l : Filter ι}
    (f : ι → MeasurableProfile (E := E) μ) (g : MeasurableProfile (E := E) μ)
    (h : Tendsto f l (𝓝 g)) : TendstoInMeasure μ (fun i => (f i).1) l g.1 := by
  have hm : ∀ i, AEMeasurable (fun x => min 1 (edist ((f i).1 x) (g.1 x))) μ :=
    fun i => aemeasurable_const.min ((f i).2.edist g.2)
  apply tendstoInMeasure_of_lintegral_min_edist _ _ hm
  apply (ENNReal.tendsto_toReal_zero_iff (fun i => integralDist_ne_top μ (f i) g)).mp
  exact tendsto_iff_dist_tendsto_zero.mp h

/-- Sequential pseudometric convergence is equivalent to convergence in measure. -/
theorem tendsto_iff_tendstoInMeasure
    (f : ℕ → MeasurableProfile (E := E) μ) (g : MeasurableProfile (E := E) μ) :
    Tendsto f atTop (𝓝 g) ↔ TendstoInMeasure μ (fun n => (f n).1) atTop g.1 := by
  constructor
  · exact tendstoInMeasure_of_tendsto μ f g
  · intro h
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply (ENNReal.tendsto_toReal_zero_iff (fun n => integralDist_ne_top μ (f n) g)).mpr
    exact tendsto_lintegral_min_edist_of_tendstoInMeasure _ _
      (fun n => aemeasurable_const.min ((f n).2.edist g.2)) h

end LatticeProb.MeasurableProfile

import LatticeProb.MeasureTheory.ProfileIntegralPseudoMetric
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Measurable integrated profile discrepancies -/

open MeasureTheory

namespace LatticeProb.MeasurableProfile

/-- A jointly measurable family has measurable integrated distance to any fixed profile. -/
theorem measurable_integralDist_toReal
    {α E Ω : Type*} [MeasurableSpace α] [PseudoEMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure α) [IsFiniteMeasure μ] (f : MeasurableProfile (E := E) μ)
    (g : Ω → MeasurableProfile (E := E) μ)
    (hg : Measurable (fun p : Ω × α => (g p.1).1 p.2)) :
    Measurable (fun ω => (integralDist μ f (g ω)).toReal) := by
  have hm : Measurable (fun p : Ω × α =>
      min 1 (edist (f.2.mk f.1 p.2) ((g p.1).1 p.2))) :=
    measurable_const.min ((f.2.measurable_mk.comp measurable_snd).edist hg)
  have hi : Measurable (fun ω => ∫⁻ x, min 1 (edist (f.2.mk f.1 x) ((g ω).1 x)) ∂μ) :=
    hm.lintegral_prod_right'
  have heq : (fun ω => ∫⁻ x, min 1 (edist (f.2.mk f.1 x) ((g ω).1 x)) ∂μ) =
      (fun ω => integralDist μ f (g ω)) := by
    funext ω
    apply lintegral_congr_ae
    filter_upwards [f.2.ae_eq_mk] with x hx
    rw [hx]
  rw [heq] at hi
  exact ENNReal.measurable_toReal.comp hi

end LatticeProb.MeasurableProfile

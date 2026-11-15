import LatticeProb.Prob.TVDominatedApproximation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Total variation approximation by measures with simple densities. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- A finite measure with a measurable density is the total variation limit of
measures with finite-valued simple densities. -/
theorem tendsto_tvDist_withDensity_eapprox {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f)
    [IsFiniteMeasure (ρ.withDensity f)] :
    Tendsto (fun n : ℕ => QuantumZipper.TV.tvDist (ρ.withDensity f)
      (ρ.withDensity (SimpleFunc.eapprox f n))) atTop (𝓝 0) := by
  apply tendsto_tvDist_of_le_of_tendsto_measure_univ
  · intro n
    apply withDensity_mono
    exact ae_of_all _ fun x => by
      rw [← SimpleFunc.iSup_eapprox_apply hf x]
      exact le_iSup (fun n => SimpleFunc.eapprox f n x) n
  · simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
      (lintegral_tendsto_of_tendsto_of_monotone (μ := ρ)
        (fun n => (SimpleFunc.eapprox f n).measurable.aemeasurable)
        (ae_of_all _ fun x i j hij => SimpleFunc.monotone_eapprox f hij x)
        (ae_of_all _ fun x => SimpleFunc.tendsto_eapprox hf x))

end LatticeProb

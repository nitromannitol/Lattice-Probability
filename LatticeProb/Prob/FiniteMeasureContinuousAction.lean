import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuous families of pushforwards of a finite measure -/

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace LatticeProb

/-- A jointly continuous family of maps sends a fixed finite measure to a weakly
continuous family of finite measures. -/
theorem continuous_finiteMeasure_map_family
    {X Z Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [PseudoMetricSpace Z] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : FiniteMeasure X) {F : X × Z → Y} (hF : Continuous F) :
    Continuous (fun z => μ.map (fun x => F (x, z))) := by
  apply FiniteMeasure.continuous_iff_forall_continuous_integral.mpr
  intro g
  rw [continuous_iff_seqContinuous]
  intro z z₀ hz
  have hm (z : Z) : Measurable (fun x : X => F (x, z)) :=
    (hF.comp (continuous_id.prodMk continuous_const)).measurable
  have hi (z : Z) : (∫ y, g y ∂(μ.map (fun x => F (x, z)) : Measure Y)) =
      ∫ x, g (F (x, z)) ∂(μ : Measure X) := by
    rw [FiniteMeasure.toMeasure_map]
    exact integral_map (hm z).aemeasurable g.continuous.aestronglyMeasurable
  simp_rw [hi]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
  · intro n
    exact (g.continuous.comp (hF.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (fun x => g.norm_coe_le_norm _)
  · exact Filter.Eventually.of_forall (fun x =>
      (g.continuous.tendsto _).comp ((hF.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hz)))

end LatticeProb

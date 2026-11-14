import LatticeProb.Prob.MarkovPathKernelDense

/-! # Continuous families of pushforward probability measures -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LatticeProb

/-- A jointly continuous transformation sends a weakly continuous family of probability
measures to a weakly continuous family of pushforward measures. -/
theorem continuous_probabilityMeasure_map_family
    {X Z Y : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] [PseudoMetricSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] [SecondCountableTopology Z]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Z → ProbabilityMeasure X} (hμ : Continuous μ)
    {F : X × Z → Y} (hF : Continuous F) :
    Continuous (fun z => (μ z).map (fun x => F (x, z))) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro g
  have h : Continuous (fun z => ∫ x, g (F (x, z)) ∂(μ z : Measure X)) :=
    continuous_integral_of_continuous_measure hμ (g.continuous.comp hF)
      (C := ‖g‖) (fun p => g.norm_coe_le_norm _)
  convert h using 1
  funext z
  rw [ProbabilityMeasure.toMeasure_map]
  have hm : Measurable (fun x : X => F (x, z)) :=
    (hF.comp (continuous_id.prodMk continuous_const)).measurable
  exact integral_map hm.aemeasurable g.continuous.aestronglyMeasurable

attribute [local instance] dUnifMetricSpace

/-- Translating a fixed law of continuous complex paths gives a weakly continuous family. -/
theorem continuous_probabilityMeasure_map_path_add
    (μ : ProbabilityMeasure C(ℝ≥0, ℂ)) :
    Continuous (fun z : ℂ => μ.map (fun b : C(ℝ≥0, ℂ) =>
      (⟨fun t => b t + z, b.continuous.add continuous_const⟩ : C(ℝ≥0, ℂ)))) := by
  apply continuous_probabilityMeasure_map_family (X := C(ℝ≥0, ℂ)) (Z := ℂ)
    (Y := C(ℝ≥0, ℂ)) (μ := fun _ : ℂ => μ)
    (F := fun p : C(ℝ≥0, ℂ) × ℂ =>
      ⟨fun t => p.1 t + p.2, p.1.continuous.add continuous_const⟩) continuous_const
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (C(ℝ≥0, ℂ) × ℂ) × ℝ≥0 => p.1.1 p.2 + p.1.2)
  fun_prop

end LatticeProb

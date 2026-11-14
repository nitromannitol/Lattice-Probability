import Mathlib
import LatticeProb.Prob.TotalVariation

/-!
# Setwise bounds and Lévy–Prokhorov distance

A setwise bound on two probability measures controls the Lévy–Prokhorov distance
between their images under a measurable map.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

variable {α X : Type*} [MeasurableSpace α] [PseudoMetricSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- Setwise closeness of two probability laws controls the distance between their images. -/
theorem levyProkhorovDist_map_le_of_setwise (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → X} (hf : Measurable f)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ B : Set X, MeasurableSet B →
      |(μ (f ⁻¹' B)).toReal - (ν (f ⁻¹' B)).toReal| ≤ δ) :
    levyProkhorovDist (μ.map f) (ν.map f) ≤ δ := by
  have : IsProbabilityMeasure (μ.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (ν.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr inferInstance
  refine levyProkhorovDist_le_of_forall_le _ _ hδ fun r B hr hB => ?_
  have hr0 : 0 < r := lt_of_le_of_lt hδ hr
  rw [Measure.map_apply hf hB, Measure.map_apply hf isOpen_thickening.measurableSet]
  have hle : (μ (f ⁻¹' B)).toReal ≤ (ν (f ⁻¹' B)).toReal + δ := by
    linarith [(abs_le.1 (h B hB)).2]
  calc μ (f ⁻¹' B)
      = ENNReal.ofReal (μ (f ⁻¹' B)).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((ν (f ⁻¹' B)).toReal + δ) := ENNReal.ofReal_le_ofReal hle
    _ = ν (f ⁻¹' B) + ENNReal.ofReal δ := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ν (f ⁻¹' thickening r B) + ENNReal.ofReal r :=
      add_le_add (measure_mono (preimage_mono (self_subset_thickening hr0 B)))
        (ENNReal.ofReal_le_ofReal hr.le)

/-- A measurable image cannot have Lévy–Prokhorov distance exceeding total variation. -/
theorem levyProkhorovDist_map_le_tvDist (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : α → X} (hf : Measurable f) :
    levyProkhorovDist (μ.map f) (ν.map f) ≤ tvDist μ ν :=
  levyProkhorovDist_map_le_of_setwise μ ν hf (tvDist_nonneg μ ν)
    (fun B _ => abs_sub_le_tvDist μ ν (f ⁻¹' B))

end LatticeProb

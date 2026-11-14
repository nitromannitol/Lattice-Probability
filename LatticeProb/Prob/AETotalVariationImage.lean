import LatticeProb.Prob.TotalVariationLevyProkhorov

/-!
# Almost-everywhere measurable images and total variation

A common almost-everywhere measurable map contracts total variation and the
Lévy–Prokhorov edistance of its image measures.
-/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A common almost-everywhere measurable image contracts total variation. -/
theorem tvDist_map_le_of_aemeasurable (μ ν : Measure α) {f : α → β}
    (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    QuantumZipper.TV.tvDist (μ.map f) (ν.map f) ≤ QuantumZipper.TV.tvDist μ ν := by
  let h := hμ.add_measure hν
  have heq := ae_add_measure_iff.mp h.ae_eq_mk
  rw [Measure.map_congr heq.1, Measure.map_congr heq.2]
  exact QuantumZipper.TV.tvDist_map_le h.measurable_mk

/-- The Lévy–Prokhorov edistance of common almost-everywhere measurable images is bounded by
 total variation of the original measures. -/
theorem levyProkhorovEDist_map_le_tvDist_of_aemeasurable [PseudoEMetricSpace β]
    (μ ν : Measure α) {f : α → β} (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    levyProkhorovEDist (μ.map f) (ν.map f) ≤ QuantumZipper.TV.tvDist μ ν :=
  (levyProkhorovEDist_le_tvDist _ _).trans (tvDist_map_le_of_aemeasurable μ ν hμ hν)

end LatticeProb

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Lévy–Prokhorov bounds for arbitrary sets

A bound for measurable sets extends to every set after enlarging the neighborhood radius.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- A Lévy–Prokhorov bound extends to an arbitrary set after increasing the neighborhood radius. -/
theorem measure_le_thickening_of_levyProkhorovEDist_lt (μ ν : Measure Ω) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (h : levyProkhorovEDist μ ν < ENNReal.ofReal δ) (A : Set Ω) :
    μ A ≤ ν (thickening (δ + ε) A) + ENNReal.ofReal δ := by
  calc
    μ A ≤ μ (thickening ε A) := measure_mono (self_subset_thickening hε A)
    _ ≤ ν (thickening δ (thickening ε A)) + ENNReal.ofReal δ := by
      simpa [ENNReal.toReal_ofReal hδ.le] using
        (left_measure_le_of_levyProkhorovEDist_lt h (isOpen_thickening.measurableSet))
    _ ≤ ν (thickening (δ + ε) A) + ENNReal.ofReal δ :=
      add_le_add (measure_mono (μ := ν) (thickening_thickening_subset δ ε A)) le_rfl

end LatticeProb

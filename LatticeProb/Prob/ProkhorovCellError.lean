import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Tactic

/-!
# Partition cell bounds from Lévy–Prokhorov distance

A bound for the distance between probability measures controls their difference on a
measurable set when the reference measure has small thickening excess on the set and
its complement.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

variable {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [OpensMeasurableSpace X]

omit [OpensMeasurableSpace X] in
/-- The discrepancy on a measurable cell is bounded by the distance tolerance plus
its largest reference-law thickening excess on either side. -/
theorem abs_measureReal_sub_le_of_levyProkhorovEDist_lt
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) (h : levyProkhorovEDist μ ν < ENNReal.ofReal δ)
    {A : Set X} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ δ + max (ν.real (thickening δ A) - ν.real A)
      (ν.real (thickening δ Aᶜ) - ν.real Aᶜ) := by
  have bound (B : Set X) (hB : MeasurableSet B) :
      μ.real B ≤ ν.real (thickening δ B) + δ := by
    have hb := left_measure_le_of_levyProkhorovEDist_lt h hB
    have hreal := ENNReal.toReal_mono (by finiteness) hb
    simpa [Measure.real, ENNReal.toReal_add, ENNReal.toReal_ofReal hδ.le] using hreal
  have h₁ := bound A hA
  have h₂ := bound Aᶜ hA.compl
  have hμ := probReal_add_probReal_compl (μ := μ) hA
  have hν := probReal_add_probReal_compl (μ := ν) hA
  have hmax₁ := le_max_left (ν.real (thickening δ A) - ν.real A)
    (ν.real (thickening δ Aᶜ) - ν.real Aᶜ)
  have hmax₂ := le_max_right (ν.real (thickening δ A) - ν.real A)
    (ν.real (thickening δ Aᶜ) - ν.real Aᶜ)
  apply abs_le.mpr
  constructor <;> linarith

end LatticeProb

import LatticeProb.Bonanno.QuantumZipper.Proofs.Section5.TVLocal
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Total variation and Lévy–Prokhorov distance

The Lévy–Prokhorov edistance is bounded by total variation, also after
applying a common measurable map.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

variable {α X : Type*} [MeasurableSpace α] [MeasurableSpace X] [PseudoEMetricSpace X]

/-- Total variation bounds Lévy–Prokhorov edistance for arbitrary measures. -/
theorem levyProkhorovEDist_le_tvDist (μ ν : Measure X) :
    levyProkhorovEDist μ ν ≤ QuantumZipper.TV.tvDist μ ν := by
  apply levyProkhorovEDist_le_of_forall μ ν
  intro ε B hε hεtop hB
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.bot_lt.ne' hεtop.ne
  have hsub : B ⊆ thickening ε.toReal B := self_subset_thickening hεpos B
  constructor
  · exact (tsub_le_iff_left.mp (QuantumZipper.TV.le_tvDist (μ := μ) (ν := ν) hB)).trans
      (add_le_add (measure_mono hsub) hε.le)
  · exact (tsub_le_iff_left.mp (QuantumZipper.TV.le_tvDist' (μ := μ) (ν := ν) hB)).trans
      (add_le_add (measure_mono hsub) hε.le)

/-- A measurable image has Lévy–Prokhorov edistance at most the original total variation. -/
theorem levyProkhorovEDist_map_le_tvDist (μ ν : Measure α) {f : α → X}
    (hf : Measurable f) :
    levyProkhorovEDist (μ.map f) (ν.map f) ≤ QuantumZipper.TV.tvDist μ ν :=
  (levyProkhorovEDist_le_tvDist _ _).trans (QuantumZipper.TV.tvDist_map_le hf)

end LatticeProb

import LatticeProb.Prob.LevyProkhorovAllSets

/-!
# Transferring Lévy–Prokhorov bounds from a metric carrier

A comparison of measures on a pseudometric carrier gives an arbitrary-set bound for the
images under any map, provided proximity on the carrier controls the target comparison.
The image map and target sets need not be measurable.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- Transfer an arbitrary-set Lévy–Prokhorov bound through a map. -/
theorem measure_preimage_le_of_levyProkhorovEDist_lt
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [OpensMeasurableSpace X]
    (μ ν : Measure X) (f : X → Y) (D : Y → Y → ℝ≥0∞) {δ ε : ℝ} {t : ℝ≥0∞}
    (hδ : 0 < δ) (hε : 0 < ε) (h : levyProkhorovEDist μ ν < ENNReal.ofReal δ)
    (hD : ∀ x y, dist x y < δ + ε → D (f y) (f x) < t) (S : Set Y) :
    μ (f ⁻¹' S) ≤ ν {x | ∃ y, f y ∈ S ∧ D (f y) (f x) < t} + ENNReal.ofReal δ := by
  calc
    μ (f ⁻¹' S) ≤ ν (thickening (δ + ε) (f ⁻¹' S)) + ENNReal.ofReal δ :=
      measure_le_thickening_of_levyProkhorovEDist_lt μ ν hδ hε h _
    _ ≤ ν {x | ∃ y, f y ∈ S ∧ D (f y) (f x) < t} + ENNReal.ofReal δ := by
      refine add_le_add (measure_mono ?_) le_rfl
      intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
      exact ⟨y, hy, hD x y hxy⟩

end LatticeProb

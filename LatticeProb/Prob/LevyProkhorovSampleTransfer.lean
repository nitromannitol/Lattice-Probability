import LatticeProb.Prob.LevyProkhorovAllSets

/-! # Lévy–Prokhorov bounds for sample-space events -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- A Lévy–Prokhorov bound for two pushforward laws controls every event in the first sample
space by the event that a sample in the second space is close to an image of that event.
No measurability assumption is needed on the event. -/
theorem measure_le_exists_edist_lt_of_levyProkhorovEDist_lt
    {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace E] [PseudoMetricSpace E] [OpensMeasurableSpace E]
    (μ : Measure Ω) (ν : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (h : levyProkhorovEDist (μ.map X) (ν.map Y) < ENNReal.ofReal δ) (B : Set Ω) :
    μ B ≤ ν {y | ∃ x ∈ B, edist (Y y) (X x) < ENNReal.ofReal (δ + ε)} +
      ENNReal.ofReal δ := by
  calc
    μ B ≤ μ.map X (X '' B) := Measure.le_map_apply_image hX.aemeasurable B
    _ ≤ ν.map Y (thickening (δ + ε) (X '' B)) + ENNReal.ofReal δ :=
      measure_le_thickening_of_levyProkhorovEDist_lt _ _ hδ hε h _
    _ = ν {y | ∃ x ∈ B, edist (Y y) (X x) < ENNReal.ofReal (δ + ε)} +
        ENNReal.ofReal δ := by
      have hset : Y ⁻¹' thickening (δ + ε) (X '' B) =
          {y | ∃ x ∈ B, edist (Y y) (X x) < ENNReal.ofReal (δ + ε)} := by
        ext y
        simp only [mem_preimage, mem_ofPred_eq, mem_thickening_iff_exists_edist_lt, mem_image]
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
          exact ⟨x, hx, hxy⟩
        · rintro ⟨x, hx, hxy⟩
          exact ⟨X x, ⟨x, hx, rfl⟩, hxy⟩
      rw [Measure.map_apply hY isOpen_thickening.measurableSet, hset]

end LatticeProb

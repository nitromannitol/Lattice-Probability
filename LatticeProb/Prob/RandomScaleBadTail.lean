import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Failure probabilities at random scales -/

open MeasureTheory Filter Topology Set

namespace LatticeProb

/-- A small random scale and small bad tails for an environment of fixed law
    give a vanishing failure probability, without any independence assumption. -/
theorem tendsto_measure_failure_of_random_scale
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E) (l : Filter ι)
    (X : ι → Ω → E) (R : ι → Ω → ℝ) (A : ι → Set Ω)
    (T : ℕ → Set E) (a : ℕ → ℝ)
    (hT : ∀ k, MeasurableSet (T k))
    (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, Measure.map (X i) P = ν)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0))
    (htail : Tendsto (fun k => ν (T k)) atTop (𝓝 0))
    (hcover : ∀ i k, A i ⊆ {ω | a k < R i ω} ∪ (X i) ⁻¹' T k) :
    Tendsto (fun i => P (A i)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_nhds_zero.1 htail _ he2).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hscale k) _ he2] with i hi
  calc
    P (A i) ≤ P {ω | a k < R i ω} + P ((X i) ⁻¹' T k) :=
      (measure_mono (hcover i k)).trans (measure_union_le _ _)
    _ = P {ω | a k < R i ω} + ν (T k) := by
      rw [← hlaw i, Measure.map_apply (hX i) (hT k)]
    _ ≤ e / 2 + e / 2 := add_le_add hi hk
    _ = e := ENNReal.add_halves e

end LatticeProb

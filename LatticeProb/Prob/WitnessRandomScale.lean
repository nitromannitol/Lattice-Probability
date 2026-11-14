import LatticeProb.Prob.WitnessScaleBadTail

/-! # Witness events at random scales -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace LatticeProb

/-- A fixed-law environment with an almost surely positive good radius remains good
at a small positive random scale, even when the environment and scale are dependent. -/
theorem tendsto_measure_witness_at_random_scale
    {Ω E W ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure Ω) (ν : Measure E) [IsFiniteMeasure ν] (l : Filter ι)
    (X : ι → Ω → E) (R : ι → Ω → ℝ) (B : Set (E × (ℝ × W)))
    (a : ℕ → ℝ) (hB : MeasurableSet B) (ha : Antitone a)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hgood : ∀ᵐ x ∂ν, ∃ δ : ℝ, 0 < δ ∧
      ∀ r w, 0 < r → r < δ → (x, r, w) ∉ B)
    (hX : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, Measure.map (X i) P = ν)
    (hR : ∀ i ω, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ w, (X i ω, R i ω, w) ∈ B}) l (𝓝 0) := by
  have hgood' : ∀ᵐ x ∂ν, ∃ n, ∀ r w, (x, r, w) ∈ B → 0 < r → r ≤ a n → False := by
    filter_upwards [hgood] with x hx
    obtain ⟨δ, hδ, hx⟩ := hx
    obtain ⟨n, hn⟩ := ha_small δ hδ
    exact ⟨n, fun r w hr hr0 hra => hx r w hr0 (lt_of_le_of_lt hra hn) hr⟩
  apply tendsto_measure_failure_of_nullMeasurable_badTail P ν l X R
    (fun i => {ω | ∃ w, (X i ω, R i ω, w) ∈ B})
    (fun n => witnessScaleBadTail B (a n)) a
  · intro n
    exact (uMeasurableSet_witnessScaleBadTail B (a n) hB) ν inferInstance
  · exact hX
  · exact hlaw
  · exact hscale
  · exact tendsto_measure_witnessScaleBadTail ν B hB a ha hgood'
  · intro i n ω hω
    by_cases h : a n < R i ω
    · exact Or.inl h
    · obtain ⟨w, hw⟩ := hω
      exact Or.inr ⟨R i ω, w, hw, hR i ω, le_of_not_gt h⟩

end LatticeProb

import LatticeProb.Prob.WitnessScaleBadTail

/-! # Witness events for varying environment laws -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb

/-- A positive random scale with vanishing upper tails avoids small-scale
witnesses when the environment laws are uniformly absolutely continuous with
respect to a finite reference law, eventually along the index filter. -/
theorem tendsto_measure_witness_of_eventually_uniform_abs_cont
    {Ω E W ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure Ω) (ν : Measure E) [IsFiniteMeasure ν] (l : Filter ι)
    (X : ι → Ω → E) (R : ι → Ω → ℝ) (B : Set (E × (ℝ × W)))
    (a : ℕ → ℝ) (hB : MeasurableSet B) (ha : Antitone a)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hgood : ∀ᵐ x ∂ν, ∃ δ : ℝ, 0 < δ ∧
      ∀ r w, 0 < r → r < δ → (x, r, w) ∉ B)
    (hcont : ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ i in l, ∀ T : Set E, NullMeasurableSet T ν → ν T ≤ d →
        P ((X i) ⁻¹' T) ≤ e)
    (hR : ∀ i, ∀ᵐ ω ∂P, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ w, (X i ω, R i ω, w) ∈ B}) l (𝓝 0) := by
  have hgood' : ∀ᵐ x ∂ν, ∃ n, ∀ r w, (x, r, w) ∈ B → 0 < r → r ≤ a n → False := by
    filter_upwards [hgood] with x hx
    obtain ⟨δ, hδ, hx⟩ := hx
    obtain ⟨n, hn⟩ := ha_small δ hδ
    exact ⟨n, fun r w hr hr0 hra => hx r w hr0 (lt_of_le_of_lt hra hn) hr⟩
  have htail := tendsto_measure_witnessScaleBadTail ν B hB a ha hgood'
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨d, hd, hcont⟩ := hcont (e / 2) he2
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 htail _ hd).exists
  have hm : NullMeasurableSet (witnessScaleBadTail B (a n)) ν :=
    (uMeasurableSet_witnessScaleBadTail B (a n) hB) ν inferInstance
  filter_upwards [hcont, ENNReal.tendsto_nhds_zero.1 (hscale n) _ he2] with i hi hs
  have hcover : {ω | ∃ w, (X i ω, R i ω, w) ∈ B} ≤ᵐ[P]
      {ω | a n < R i ω} ∪ (X i) ⁻¹' witnessScaleBadTail B (a n) := by
    filter_upwards [hR i] with ω hr hω
    by_cases h : a n < R i ω
    · exact Or.inl h
    · obtain ⟨w, hw⟩ := hω
      exact Or.inr ⟨R i ω, w, hw, hr, le_of_not_gt h⟩
  calc
    P {ω | ∃ w, (X i ω, R i ω, w) ∈ B} ≤
        P {ω | a n < R i ω} + P ((X i) ⁻¹' witnessScaleBadTail B (a n)) :=
      (measure_mono_ae hcover).trans (measure_union_le _ _)
    _ ≤ e / 2 + e / 2 := add_le_add hs (hi _ hm hn)
    _ = e := ENNReal.add_halves e

end LatticeProb

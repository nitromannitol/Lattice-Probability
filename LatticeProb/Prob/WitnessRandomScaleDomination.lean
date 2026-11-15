import LatticeProb.Prob.WitnessRandomScaleContiguity

/-! # Random-scale witnesses under a dominating environment law -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace LatticeProb

/-- A finite dominating law, absolutely continuous with respect to a reference
law, transfers its almost-sure good-radius estimate to varying distributions. -/
theorem tendsto_measure_witness_of_eventually_dominated
    {Ω E W ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure Ω) (ν μ : Measure E) [IsFiniteMeasure μ] (l : Filter ι)
    (X : ι → Ω → E) (R : ι → Ω → ℝ) (B : Set (E × (ℝ × W)))
    (a : ℕ → ℝ) (hB : MeasurableSet B) (ha : Antitone a)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hgood : ∀ᵐ x ∂ν, ∃ δ : ℝ, 0 < δ ∧
      ∀ r w, 0 < r → r < δ → (x, r, w) ∉ B)
    (hac : μ ≪ ν) (hX : ∀ i, AEMeasurable (X i) P)
    (hdom : ∀ᶠ i in l, Measure.map (X i) P ≤ μ)
    (hR : ∀ i, ∀ᵐ ω ∂P, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ w, (X i ω, R i ω, w) ∈ B}) l (𝓝 0) := by
  apply tendsto_measure_witness_of_eventually_uniform_abs_cont P μ l X R B a hB ha
    ha_small (hac.ae_le hgood) ?_ hR hscale
  intro e he
  refine ⟨e, he, ?_⟩
  filter_upwards [hdom] with i hi T hT hsmall
  rw [← Measure.map_apply₀ (hX i) (hT.mono hi)]
  exact (hi T).trans hsmall

end LatticeProb

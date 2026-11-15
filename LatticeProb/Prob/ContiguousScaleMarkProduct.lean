import LatticeProb.Prob.WitnessRandomScaleContiguity

/-! # Products of small scales and varying marks -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb

/-- A small positive random scale times a measurable real mark tends to zero in
probability when the varying environment laws are uniformly absolutely
continuous relative to a finite reference law. The scale and mark may depend
on each other. -/
theorem tendsto_measure_scale_mul_abs_mark_of_eventually_uniform_abs_cont
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [StandardBorelSpace E]
    (P : Measure Ω) (ν : Measure E) [IsFiniteMeasure ν] (l : Filter ι)
    (X : ι → Ω → E) (R : ι → Ω → ℝ) (m : E → ℝ) (hm : Measurable m)
    (a : ℕ → ℝ) (ha : Antitone a)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hcont : ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ i in l, ∀ T : Set E, NullMeasurableSet T ν → ν T ≤ d →
        P ((X i) ⁻¹' T) ≤ e)
    (hR : ∀ i, ∀ᵐ ω ∂P, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i => P {ω | ε < R i ω * |m (X i ω)|}) l (𝓝 0) := by
  let B : Set (E × (ℝ × Unit)) := {p | ε < p.2.1 * |m p.1|}
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const
      (measurable_fst.comp measurable_snd |>.mul (continuous_abs.measurable.comp (hm.comp measurable_fst)))
  have hgood : ∀ᵐ x ∂ν, ∃ δ : ℝ, 0 < δ ∧
      ∀ r w, 0 < r → r < δ → (x, r, w) ∉ B := by
    apply ae_of_all
    intro x
    have hden : 0 < |m x| + 1 := by positivity
    refine ⟨ε / (|m x| + 1), div_pos hε hden, ?_⟩
    intro r w hr hrδ hbad
    have hbound : r * (|m x| + 1) < ε := (lt_div_iff₀ hden).mp hrδ
    change ε < r * |m x| at hbad
    nlinarith
  have h := tendsto_measure_witness_of_eventually_uniform_abs_cont
    P ν l X R B a hB ha ha_small hgood hcont hR hscale
  simpa only [B, mem_ofPred_eq, exists_const] using h

end LatticeProb

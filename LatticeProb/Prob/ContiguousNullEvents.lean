import LatticeProb.Prob.WitnessRandomScaleContiguity

/-! # Null events under varying laws -/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb

/-- Eventual uniform absolute continuity makes the preimage measure of a
reference-null event tend to zero. -/
theorem tendsto_measure_preimage_of_null_of_eventually_uniform_abs_cont
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E) (l : Filter ι) (X : ι → Ω → E)
    (hcont : ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ i in l, ∀ T : Set E, NullMeasurableSet T ν → ν T ≤ d →
        P ((X i) ⁻¹' T) ≤ e)
    {T : Set E} (hT : NullMeasurableSet T ν) (hnull : ν T = 0) :
    Tendsto (fun i => P ((X i) ⁻¹' T)) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨d, _, h⟩ := hcont e he
  filter_upwards [h] with i hi
  exact hi T hT (by rw [hnull]; exact zero_le)

end LatticeProb

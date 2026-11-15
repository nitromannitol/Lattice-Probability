import LatticeProb.LQG.JointShiftedWalkRandomScale
import LatticeProb.Prob.WitnessRandomScaleContiguity

/-! # Shifted walk witnesses under varying environment laws -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- Uniform absolute continuity of varying environment laws transfers a good-radius
condition to dependent, almost surely positive random scales tending to zero. -/
theorem tendsto_measure_jointShiftedWalk_witness_of_eventually_uniform_abs_cont
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : Measure JointShiftedWalkEnvironment) [IsFiniteMeasure ν]
    (l : Filter ι) (X : ι → Ω → JointShiftedWalkEnvironment) (R : ι → Ω → ℝ)
    {U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞)
    (a : ℕ → ℝ) (ha : Antitone a)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hgood : ∀ᵐ e ∂ν, ∃ δ : ℝ, 0 < δ ∧ ∀ r j, 0 < r → r < δ →
      ¬ (scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K ∧
        jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (e, r, j))
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} ≤ t))
    (hcont : ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ i in l, ∀ T : Set JointShiftedWalkEnvironment, NullMeasurableSet T ν → ν T ≤ d →
        P ((X i) ⁻¹' T) ≤ e)
    (hR : ∀ i, ∀ᵐ ω ∂P, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (X i ω, R i ω, j))
        {ξ | (jointShiftedWalkWitnessOf (X i ω, R i ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ξ) ∈ U} ≤ t})
      l (𝓝 0) := by
  have : StandardBorelSpace C(ℝ, ℂ) := inferInstance
  have : StandardBorelSpace JointShiftedWalkEnvironment := inferInstance
  exact tendsto_measure_witness_of_eventually_uniform_abs_cont P ν l X R
    {z | scaledWalkStart (jointShiftedWalkWitnessOf z).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf z)
        {ξ | (jointShiftedWalkWitnessOf z,
          scaledWalkPath (jointShiftedWalkWitnessOf z).2 ξ) ∈ U} ≤ t}
    a (measurableSet_jointShiftedWalkWitnessOf hU hK t) ha ha_small hgood hcont hR hscale

end LatticeProb

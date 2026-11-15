import LatticeProb.LQG.JointShiftedWalkRandomScale
import LatticeProb.Prob.WitnessRandomScaleAE

/-! # Shifted walk witnesses at almost surely positive random scales -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- A common-law environment with almost surely good small radii has vanishing
walk witness probability at dependent almost surely positive random scales tending to zero. -/
theorem tendsto_measure_jointShiftedWalk_witness_at_ae_positive_random_scale
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
    (hX : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, Measure.map (X i) P = ν)
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
  exact tendsto_measure_witness_at_ae_positive_random_scale P ν l X R
    {z | scaledWalkStart (jointShiftedWalkWitnessOf z).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf z)
        {ξ | (jointShiftedWalkWitnessOf z,
          scaledWalkPath (jointShiftedWalkWitnessOf z).2 ξ) ∈ U} ≤ t}
    a (measurableSet_jointShiftedWalkWitnessOf hU hK t) ha ha_small hgood hX hlaw hR hscale

end LatticeProb

import LatticeProb.LQG.JointShiftedWalkRandomScaleVarying
import LatticeProb.LQG.ConeSmallMassProbability

/-! # Shifted walk witnesses at quantum-cone scales -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology ProbabilityTheory
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling
open scoped ENNReal NNReal

namespace LatticeProb

/-- Small-mass cone scales avoid walk witnesses under a good-radius condition
and uniform absolute continuity of the varying environment laws. -/
theorem tendsto_measure_jointShiftedWalk_witness_at_coneScale
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure JointShiftedWalkEnvironment) [IsFiniteMeasure ν]
    (X : ℕ → Ω → JointShiftedWalkEnvironment)
    {γ α : ℝ} (hγ : 0 < γ) (hα : α < lqgQ γ)
    {B B' : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝[>] 0))
    {U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))} (hU : MeasurableSet U)
    {K : Set ℂ} (hK : MeasurableSet K) (t : ℝ≥0∞)
    (a : ℕ → ℝ) (ha : Antitone a) (ha_pos : ∀ k, 0 < a k)
    (ha_small : ∀ δ : ℝ, 0 < δ → ∃ n, a n < δ)
    (hgood : ∀ᵐ e ∂ν, ∃ δ : ℝ, 0 < δ ∧ ∀ r j, 0 < r → r < δ →
      ¬ (scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K ∧
        jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (e, r, j))
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} ≤ t))
    (hcont : ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ n in atTop, ∀ T : Set JointShiftedWalkEnvironment,
        NullMeasurableSet T ν → ν T ≤ d → P ((X n) ⁻¹' T) ≤ e) :
    Tendsto (fun n => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf
        (X n ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n), j)).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf
        (X n ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n), j))
        {ξ | (jointShiftedWalkWitnessOf
          (X n ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n), j),
          scaledWalkPath (jointShiftedWalkWitnessOf
            (X n ω, coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n), j)).2 ξ) ∈ U} ≤ t})
      atTop (𝓝 0) := by
  apply tendsto_measure_jointShiftedWalk_witness_of_eventually_uniform_abs_cont
    P ν atTop X (fun n ω => coneScale γ α (fun t => B t ω) (fun t => B' t ω) (b n))
    hU hK t a ha ha_small hgood hcont
  · intro n
    exact ae_of_all P (fun ω => Real.exp_pos _)
  · intro k
    exact tendsto_measure_coneScale_gt_zero hγ hα hB hB' hb (ha_pos k)

end LatticeProb

import LatticeProb.LQG.JointShiftedWalkConeScale
import LatticeProb.Prob.ContiguousNullEvents

/-! # Shifted walk witnesses and mesh positivity at cone scales -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology ProbabilityTheory
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling
open scoped ENNReal NNReal

namespace LatticeProb

/-- Small-mass cone scales avoid walk witnesses and nonpositive meshes under
a good-radius condition and uniform absolute continuity of the varying laws. -/
theorem tendsto_jointShiftedWalk_witness_and_badMesh_at_coneScale
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
    (hmesh : ∀ᵐ e ∂ν, 0 < e.2.1.2.1)
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
      atTop (𝓝 0) ∧
    Tendsto (fun n => P {ω | (X n ω).2.1.2.1 ≤ 0}) atTop (𝓝 0) := by
  constructor
  · exact tendsto_measure_jointShiftedWalk_witness_at_coneScale
      P ν X hγ hα hB hB' b hb hU hK t a ha ha_pos ha_small hgood hcont
  · have hnull : ν {e : JointShiftedWalkEnvironment | e.2.1.2.1 ≤ 0} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hmesh)
      intro e he
      exact not_lt_of_ge he
    have hmeas : MeasurableSet {e : JointShiftedWalkEnvironment | e.2.1.2.1 ≤ 0} :=
      measurableSet_le measurable_snd.fst.snd.fst measurable_const
    exact tendsto_measure_preimage_of_null_of_eventually_uniform_abs_cont P ν atTop X hcont
      hmeas.nullMeasurableSet hnull

end LatticeProb

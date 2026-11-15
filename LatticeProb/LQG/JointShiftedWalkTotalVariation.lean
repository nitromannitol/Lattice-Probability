import LatticeProb.LQG.JointShiftedWalkRandomScaleVarying
import LatticeProb.Prob.TotalVariationContiguity
import LatticeProb.Prob.ContiguousNullEvents

/-! # Shifted walk witnesses under total variation convergence -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- Total variation convergence transfers both the good-radius witness estimate
and almost-sure positivity of the reference mesh to varying environments. -/
theorem tendsto_jointShiftedWalk_witness_and_badMesh_of_tendsto_tvDist
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
    (hmesh : ∀ᵐ e ∂ν, 0 < e.2.1.2.1)
    (hX : ∀ i, AEMeasurable (X i) P)
    (htv : Tendsto (fun i => QuantumZipper.TV.tvDist (Measure.map (X i) P) ν)
      l (𝓝 0))
    (hR : ∀ i, ∀ᵐ ω ∂P, 0 < R i ω)
    (hscale : ∀ k, Tendsto (fun i => P {ω | a k < R i ω}) l (𝓝 0)) :
    Tendsto (fun i => P {ω | ∃ j,
      scaledWalkStart (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ∈ K ∧
      jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (X i ω, R i ω, j))
        {ξ | (jointShiftedWalkWitnessOf (X i ω, R i ω, j),
          scaledWalkPath (jointShiftedWalkWitnessOf (X i ω, R i ω, j)).2 ξ) ∈ U} ≤ t})
      l (𝓝 0) ∧
    Tendsto (fun i => P {ω | (X i ω).2.1.2.1 ≤ 0}) l (𝓝 0) := by
  have hcont : ∀ e : ℝ≥0∞, 0 < e → ∃ d : ℝ≥0∞, 0 < d ∧
      ∀ᶠ i in l, ∀ T : Set JointShiftedWalkEnvironment, NullMeasurableSet T ν → ν T ≤ d →
        P ((X i) ⁻¹' T) ≤ e := by
    intro e he
    obtain ⟨d, hd, h⟩ := eventually_preimage_measure_le_of_tendsto_tvDist P ν l X hX htv e he
    refine ⟨d, hd, ?_⟩
    filter_upwards [h] with i hi T _ hT
    exact hi T hT
  constructor
  · exact tendsto_measure_jointShiftedWalk_witness_of_eventually_uniform_abs_cont
      P ν l X R hU hK t a ha ha_small hgood hcont hR hscale
  · have hnull : ν {e : JointShiftedWalkEnvironment | e.2.1.2.1 ≤ 0} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hmesh)
      intro e he
      exact not_lt_of_ge he
    have hmeas : MeasurableSet {e : JointShiftedWalkEnvironment | e.2.1.2.1 ≤ 0} :=
      measurableSet_le measurable_snd.fst.snd.fst measurable_const
    exact tendsto_measure_preimage_of_null_of_eventually_uniform_abs_cont P ν l X hcont
      hmeas.nullMeasurableSet hnull

end LatticeProb

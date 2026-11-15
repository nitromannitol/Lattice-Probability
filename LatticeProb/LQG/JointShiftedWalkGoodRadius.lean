import LatticeProb.LQG.JointShiftedWalkRandomScale

/-! # Local finiteness and shifted-walk witnesses -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open MatedCRTHarmonic
open scoped ENNReal NNReal

namespace LatticeProb

/-- Absence of a low-probability witness at an anchor is equivalent to local
finiteness and a strict graph-walk probability bound at that anchor. -/
theorem not_jointShiftedWalk_witness_iff (q : JointShiftedWalkWitness)
    (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) (K : Set ℂ) (t : ℝ≥0∞) :
    (¬ (scaledWalkStart q.2 ∈ K ∧
      jointShiftedVertexWalkKernel q {ξ | (q, scaledWalkPath q.2 ξ) ∈ U} ≤ t)) ↔
    (scaledWalkStart q.2 ∈ K →
      ∃ h : MatedCRT.IsLocallyFinite 1
          (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2),
        t < ((MatedCRT.graph 1 (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2) h).walkLaw
          q.2.2.2).map
          (MatedCRT.graph 1 (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2) h).vertexPath
          {ξ | (q, scaledWalkPath q.2 ξ) ∈ U}) := by
  classical
  constructor
  · intro hn hK
    by_cases h : MatedCRT.IsLocallyFinite 1
        (shiftedMeshPath q.1 q.2.1.1.2.1 q.2.1.1.2.2)
    · refine ⟨h, ?_⟩
      rw [← jointShiftedVertexWalkKernel_apply q h]
      exact lt_of_not_ge (fun ht => hn ⟨hK, ht⟩)
    · have hz := jointShiftedVertexWalkKernel_apply_of_not_locallyFinite q h
      exact False.elim (hn ⟨hK, by rw [hz]; exact zero_le⟩)
  · intro hh ⟨hK, ht⟩
    obtain ⟨h, hp⟩ := hh hK
    rw [← jointShiftedVertexWalkKernel_apply q h] at hp
    exact (not_le_of_gt hp) ht

/-- The small-radius witness condition can be checked using the graph law on
locally finite graphs, uniformly over all starting vertices. -/
theorem jointShiftedWalk_goodRadius_iff (e : JointShiftedWalkEnvironment)
    (δ : ℝ) (U : Set (JointShiftedWalkWitness × C(ℝ≥0, ℂ))) (K : Set ℂ)
    (t : ℝ≥0∞) :
    (∀ r j, 0 < r → r < δ →
      ¬ (scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K ∧
        jointShiftedVertexWalkKernel (jointShiftedWalkWitnessOf (e, r, j))
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U} ≤ t)) ↔
    (∀ r j, 0 < r → r < δ →
      scaledWalkStart (jointShiftedWalkWitnessOf (e, r, j)).2 ∈ K →
      ∃ h : MatedCRT.IsLocallyFinite 1
          (shiftedMeshPath e.1 e.2.1.2.1 e.2.1.2.2),
        t < ((MatedCRT.graph 1 (shiftedMeshPath e.1 e.2.1.2.1 e.2.1.2.2) h).walkLaw j).map
          (MatedCRT.graph 1 (shiftedMeshPath e.1 e.2.1.2.1 e.2.1.2.2) h).vertexPath
          {ξ | (jointShiftedWalkWitnessOf (e, r, j),
            scaledWalkPath (jointShiftedWalkWitnessOf (e, r, j)).2 ξ) ∈ U}) := by
  constructor
  · intro hh r j hr hrδ
    exact (not_jointShiftedWalk_witness_iff (jointShiftedWalkWitnessOf (e, r, j)) U K t).mp
      (hh r j hr hrδ)
  · intro hh r j hr hrδ
    exact (not_jointShiftedWalk_witness_iff (jointShiftedWalkWitnessOf (e, r, j)) U K t).mpr
      (hh r j hr hrδ)

end LatticeProb

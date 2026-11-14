import LatticeProb.LQG.ShiftedMeshWalkWeights
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableGraph

/-! # Measurable domains for walks on shifted grids -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open MatedCRTHarmonic MatedCRTHarmonic.CellScaling

namespace LatticeProb

/-- Local finiteness of the graph is jointly measurable in the path and shifted grid. -/
theorem measurableSet_shiftedMesh_isLocallyFinite :
    MeasurableSet {p : MatedCRT.Path2 × ℝ × ℝ |
      MatedCRT.IsLocallyFinite 1 (shiftedMeshPath p.1 p.2.1 p.2.2)} :=
  (measurableSet_matedCRT_isLocallyFinite 1).preimage continuous_shiftedMeshPath.measurable

/-- Candidate start states are always valid; a dart requires its labelled edge to exist. -/
def shiftedMeshCodeValid (p : MatedCRT.Path2 × ℝ × ℝ) : MeshGridStateCode → Prop
  | Sum.inl _ => True
  | Sum.inr d => shiftedMeshEdgeCode p.1 p.2.1 p.2.2 d.1 = true

/-- A candidate prefix is valid when all of its states are valid. -/
def shiftedMeshCodePrefixValid (p : MatedCRT.Path2 × ℝ × ℝ)
    (s : ℕ → MeshGridStateCode) (n : ℕ) : Prop :=
  ∀ i ≤ n, shiftedMeshCodeValid p (s i)

/-- Validity of a fixed coded state is jointly measurable in the shifted grid. -/
theorem measurableSet_shiftedMeshCodeValid (s : MeshGridStateCode) :
    MeasurableSet {p : MatedCRT.Path2 × ℝ × ℝ | shiftedMeshCodeValid p s} := by
  cases s with
  | inl x => simp [shiftedMeshCodeValid]
  | inr d =>
    exact (measurableSet_singleton true).preimage (measurable_shiftedMeshEdgeCode.eval (a := d.1))

/-- Validity of a fixed finite coded prefix is jointly measurable in the shifted grid. -/
theorem measurableSet_shiftedMeshCodePrefixValid (s : ℕ → MeshGridStateCode) (n : ℕ) :
    MeasurableSet {p : MatedCRT.Path2 × ℝ × ℝ | shiftedMeshCodePrefixValid p s n} := by
  rw [show {p : MatedCRT.Path2 × ℝ × ℝ | shiftedMeshCodePrefixValid p s n} =
      ⋂ i : Fin (n + 1), {p | shiftedMeshCodeValid p (s i)} by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, shiftedMeshCodePrefixValid]
    constructor
    · intro h i
      exact h i (Nat.lt_succ_iff.mp i.isLt)
    · intro h i hi
      exact h ⟨i, Nat.lt_succ_iff.mpr hi⟩]
  exact MeasurableSet.iInter (fun i => measurableSet_shiftedMeshCodeValid (s i))

end LatticeProb

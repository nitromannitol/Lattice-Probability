import LatticeProb.Prob.BrownianParentBlockInitialGeometry
import LatticeProb.Euclidean.ParentBlockDiameter

/-! # Parent-block excursion geometry from an interior point -/

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A path starting in a parent-block interior stays within six side lengths
of its initial point through its finite first exit from that interior. -/
theorem interior_parentBlock_exit_geometry (c : ℂ) (s : ℝ) (hs : 0 < s)
    (z : Euc 2) (ω : BrownianPath 2)
    (hstart : Complex.orthonormalBasisOneI.repr.symm (z + ω 0) ∈
      interior (LatticeProb.ParentBlock.parentBlock c s))
    (hfinite : continuousExitTime
      (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
        interior (LatticeProb.ParentBlock.parentBlock c s)) z ω ≠ ∞) :
    let U := Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      interior (LatticeProb.ParentBlock.parentBlock c s)
    let τ := (continuousExitTime U z ω).toNNReal
    Complex.orthonormalBasisOneI.repr.symm (z + ω τ) ∉
        interior (LatticeProb.ParentBlock.parentBlock c s) ∧
    ∀ t ∈ Icc 0 τ, ‖Complex.orthonormalBasisOneI.repr.symm (z + ω t) -
        Complex.orthonormalBasisOneI.repr.symm (z + ω 0)‖ ≤ 6 * s := by
  let U : Set (Euc 2) := Complex.orthonormalBasisOneI.repr.symm ⁻¹'
    interior (LatticeProb.ParentBlock.parentBlock c s)
  have hU : IsOpen U := isOpen_interior.preimage
    Complex.orthonormalBasisOneI.repr.symm.continuous
  have hstartU : z + ω 0 ∈ U := hstart
  have hclosed : IsClosed (Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      LatticeProb.ParentBlock.parentBlock c s) := by
    have hc : IsClosed (LatticeProb.ParentBlock.parentBlock c s) := by
      rw [LatticeProb.ParentBlock.parentBlock_eq hs.le]
      exact LatticeProb.ParentBlock.isClosed_closedSquare _ _
    exact hc.preimage Complex.orthonormalBasisOneI.repr.symm.continuous
  have hsub : U ⊆ Complex.orthonormalBasisOneI.repr.symm ⁻¹'
      LatticeProb.ParentBlock.parentBlock c s := by
    intro x hx
    change Complex.orthonormalBasisOneI.repr.symm x ∈
      LatticeProb.ParentBlock.parentBlock c s
    exact interior_subset hx
  refine ⟨continuousExitTime_not_mem hU hfinite, ?_⟩
  intro t ht
  obtain ⟨u, hu⟩ := mem_range_stoppedBrownianRepresentative U z ω ht.2
  have hmem : z + ω t ∈ closure U :=
    hu ▸ stoppedBrownianRepresentative_mem_closure hU hstartU hfinite u
  exact LatticeProb.ParentBlock.norm_sub_le_six_mul_of_mem_parentBlock hs.le
    (interior_subset hstart) (closure_minimal hsub hclosed hmem)

end BouRabeeGwynne

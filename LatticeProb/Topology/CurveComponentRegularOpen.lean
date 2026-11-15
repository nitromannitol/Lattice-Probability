import LatticeProb.Topology.CurveComponentFrontier
import Mathlib.Topology.Connected.LocallyConnected

/-! # Interiors of closures of planar components -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- Every component of the interior of a closed planar set is regular open. -/
theorem interior_closure_component_interior {K : Set ℂ} (hK : IsClosed K) (x : ℂ) :
    interior (closure (connectedComponentIn (interior K) x)) =
      connectedComponentIn (interior K) x := by
  let U := connectedComponentIn (interior K) x
  have hU : IsOpen U := isOpen_interior.connectedComponentIn
  have hUK : closure U ⊆ K :=
    hK.closure_subset_iff.mpr ((connectedComponentIn_subset (interior K) x).trans interior_subset)
  apply Subset.antisymm
  · intro z hz
    have hzK : z ∈ interior K := interior_mono hUK hz
    by_contra hzU
    have hzfront : z ∈ frontier U := by
      rw [frontier]
      exact ⟨interior_subset hz, fun hzint => hzU (interior_subset hzint)⟩
    have hzfrontK := frontier_component_interior_subset hK x hzfront
    exact hzfrontK.2 hzK
  · exact interior_maximal subset_closure hU

/-- If a curve segment is the closure of an interior component, its interior is
that component. -/
theorem interior_image_eq_component_of_image_eq_closure
    {T : Type*} (f : T → ℂ) (A : Set T) {K : Set ℂ} (hK : IsClosed K)
    (x : ℂ) (himage : f '' A = closure (connectedComponentIn (interior K) x)) :
    interior (f '' A) = connectedComponentIn (interior K) x := by
  rw [himage, interior_closure_component_interior hK x]

end LatticeProb

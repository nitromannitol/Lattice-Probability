import Mathlib.Topology.Closure
import Mathlib.Data.Set.Lattice.Disjoint

/-! Disjointness of interiors for unions of regular closed sets. -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- If a regular closed set has interior disjoint from the interior of each regular closed set in
an arbitrary family, it is disjoint from the interior of their union. -/
theorem disjoint_interior_iUnion_of_regularClosed
    {X ι : Type*} [TopologicalSpace X] {A : Set X} {K : ι → Set X}
    (hA : closure (interior A) = A) (hK : ∀ i, closure (interior (K i)) = K i)
    (hdis : ∀ i, Disjoint (interior A) (interior (K i))) :
    Disjoint (interior (⋃ i, K i)) A := by
  have h : Disjoint (interior A) (⋃ i, K i) := by
    apply disjoint_iUnion_right.mpr
    intro i
    rw [← hK i]
    exact (hdis i).closure_right isOpen_interior
  have h' : Disjoint (closure (interior A)) (interior (⋃ i, K i)) :=
    (h.mono_right interior_subset).closure_left isOpen_interior
  rw [hA] at h'
  exact h'.symm

end LatticeProb

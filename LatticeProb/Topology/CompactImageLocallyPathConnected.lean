import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Separation.Hausdorff

/-! # Locally path-connected compact images -/

set_option autoImplicit false

open Set

namespace LatticeProb.Topology

/-- A continuous image of a compact locally path-connected space in a
Hausdorff space is locally path-connected. -/
theorem locallyPathConnectedSpace_range {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [LocallyPathConnectedSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) : LocallyPathConnectedSpace (range f) := by
  let g : X → range f := fun x => ⟨f x, mem_range_self x⟩
  have hg : Continuous g := hf.subtype_mk (fun x => mem_range_self x)
  have hsurj : Function.Surjective g := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  exact (Topology.IsQuotientMap.of_surjective_continuous hsurj hg).locallyPathConnectedSpace

/-- The image of a continuous path on a compact real interval is locally
path-connected, including for empty or singleton intervals. -/
theorem locallyPathConnectedSpace_image_Icc {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f : ℝ → Y} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : LocallyPathConnectedSpace (f '' Icc a b) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : LocallyPathConnectedSpace (Icc a b) := (convex_Icc a b).locallyPathConnectedSpace
  let g : Icc a b → Y := fun x => f x
  have hg : Continuous g := hf.domRestrict
  have hrange : range g = f '' Icc a b := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange]
  exact locallyPathConnectedSpace_range hg

end LatticeProb.Topology

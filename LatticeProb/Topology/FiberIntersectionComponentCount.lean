import LatticeProb.Topology.HomeomorphComponentCount
import LatticeProb.Topology.QuotientFiberHomeomorphism
import Mathlib.Topology.Maps.Proper.Basic

/-! # Intersection component counts from fibers -/

set_option autoImplicit false

open Function Set TopologicalSpace Topology

namespace LatticeProb

/-- Quotient maps with the same fibers give the same number of non-singleton
components in the intersections of the images of two parameter sets. -/
theorem ncard_inter_components_of_quotient_maps_same_fibers
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (A B : Set X) :
    {C ∈ connectedComponentIn (f '' A ∩ f '' B) '' (f '' A ∩ f '' B) |
        ¬ C.Subsingleton}.ncard =
    {C ∈ connectedComponentIn (g '' A ∩ g '' B) '' (g '' A ∩ g '' B) |
        ¬ C.Subsingleton}.ncard := by
  obtain ⟨e, he⟩ := exists_homeomorph_of_quotient_maps_same_fibers f g hf hg hfg
  have hA : e '' (f '' A) = g '' A := by
    rw [image_image]
    exact image_congr (fun x _ => he x)
  have hB : e '' (f '' B) = g '' B := by
    rw [image_image]
    exact image_congr (fun x _ => he x)
  have hc := ncard_nonsubsingleton_inter_components_image e (f '' A) (f '' B)
  rw [hA, hB] at hc
  exact hc.symm

/-- Proper surjections with the same fibers give the same intersection component
counts for the images of two parameter sets. -/
theorem ncard_inter_components_of_proper_maps_same_fibers
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfs : Surjective f) (hgs : Surjective g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (A B : Set X) :
    {C ∈ connectedComponentIn (f '' A ∩ f '' B) '' (f '' A ∩ f '' B) |
        ¬ C.Subsingleton}.ncard =
    {C ∈ connectedComponentIn (g '' A ∩ g '' B) '' (g '' A ∩ g '' B) |
        ¬ C.Subsingleton}.ncard :=
  ncard_inter_components_of_quotient_maps_same_fibers f g
    (hf.isClosedMap.isQuotientMap hf.continuous hfs)
    (hg.isClosedMap.isQuotientMap hg.continuous hgs) hfg A B

end LatticeProb

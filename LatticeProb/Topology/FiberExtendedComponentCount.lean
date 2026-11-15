import LatticeProb.Topology.ComplexCompactComponentCount
import LatticeProb.Topology.QuotientFiberHomeomorphism
import Mathlib.Topology.Maps.Proper.Basic

/-! # Extended intersection component counts from fibers -/

set_option autoImplicit false

open Function Set TopologicalSpace Topology

namespace LatticeProb

/-- Quotient maps with the same fibers preserve the extended number of
non-singleton components in intersections of images of parameter sets. -/
theorem encard_inter_components_of_quotient_maps_same_fibers
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (A B : Set X) :
    (nonSingletonComponents (f '' A ∩ f '' B)).encard =
      (nonSingletonComponents (g '' A ∩ g '' B)).encard := by
  obtain ⟨e, he⟩ := exists_homeomorph_of_quotient_maps_same_fibers f g hf hg hfg
  have hA : e '' (f '' A) = g '' A := by
    rw [image_image]
    exact image_congr (fun x _ => he x)
  have hB : e '' (f '' B) = g '' B := by
    rw [image_image]
    exact image_congr (fun x _ => he x)
  have hinj : Injective (fun C : Set Y => e '' C) := e.injective.image_injective
  have hc := nonSingletonComponents_image_homeomorph e (f '' A ∩ f '' B)
  rw [image_inter e.injective, hA, hB] at hc
  rw [hc, Set.InjOn.encard_image hinj.injOn]

/-- Proper surjections with the same fibers preserve extended intersection
component counts. -/
theorem encard_inter_components_of_proper_maps_same_fibers
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfs : Surjective f) (hgs : Surjective g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (A B : Set X) :
    (nonSingletonComponents (f '' A ∩ f '' B)).encard =
      (nonSingletonComponents (g '' A ∩ g '' B)).encard :=
  encard_inter_components_of_quotient_maps_same_fibers f g
    (hf.isClosedMap.isQuotientMap hf.continuous hfs)
    (hg.isClosedMap.isQuotientMap hg.continuous hgs) hfg A B

end LatticeProb

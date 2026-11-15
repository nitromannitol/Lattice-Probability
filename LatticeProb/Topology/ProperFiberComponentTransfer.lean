import LatticeProb.Topology.QuotientFiberHomeomorphism
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.Basic

/-! # Component transport for proper maps with equal fibres -/

set_option autoImplicit false

open Function Set Topology

namespace LatticeProb

/-- Proper surjections with equal fibres induce a homeomorphism preserving both the
parameter and the connected component of the interior of every parameter-set image. -/
theorem exists_homeomorph_of_proper_maps_same_fibers_components
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfs : Surjective f) (hgs : Surjective g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) :
    ∃ e : Y ≃ₜ Z, (∀ x, e (f x) = g x) ∧
      ∀ (S : Set X) (u : X), f u ∈ interior (f '' S) →
        e '' connectedComponentIn (interior (f '' S)) (f u) =
          connectedComponentIn (interior (g '' S)) (g u) := by
  obtain ⟨e, he⟩ := exists_homeomorph_of_quotient_maps_same_fibers f g
    (hf.isClosedMap.isQuotientMap hf.continuous hfs)
    (hg.isClosedMap.isQuotientMap hg.continuous hgs) hfg
  refine ⟨e, he, ?_⟩
  intro S u hu
  have himage : e '' (f '' S) = g '' S := by
    rw [image_image]
    exact image_congr (fun x _ => he x)
  rw [e.image_connectedComponentIn hu, e.image_interior, himage, he u]

/-- A representation of a component closure by a parameter-set image transfers
between proper surjections with equal fibres, using the same parameter sets. -/
theorem image_eq_componentClosure_of_proper_maps_same_fibers
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsProperMap f) (hg : IsProperMap g)
    (hfs : Surjective f) (hgs : Surjective g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) (S T : Set X) (u : X)
    (hu : f u ∈ interior (f '' S))
    (hT : f '' T = closure (connectedComponentIn (interior (f '' S)) (f u))) :
    g '' T = closure (connectedComponentIn (interior (g '' S)) (g u)) := by
  obtain ⟨e, he, hc⟩ :=
    exists_homeomorph_of_proper_maps_same_fibers_components f g hf hg hfs hgs hfg
  have himage : e '' (f '' T) = g '' T := by
    rw [image_image]
    exact image_congr (fun x _ => he x)
  calc
    g '' T = e '' (f '' T) := himage.symm
    _ = e '' closure (connectedComponentIn (interior (f '' S)) (f u)) := by rw [hT]
    _ = closure (e '' connectedComponentIn (interior (f '' S)) (f u)) := e.image_closure _
    _ = closure (connectedComponentIn (interior (g '' S)) (g u)) := by rw [hc S u hu]

end LatticeProb

import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered

/-! # Interior points of images of closed maps -/

set_option autoImplicit false

open Function Set

namespace LatticeProb

/-- A closed surjection maps a fibre contained in the interior of a set to an
interior point of the image of that set. -/
theorem mem_interior_image_of_fiber_subset_interior
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsClosedMap f) (hs : Surjective f)
    (S : Set X) (u : X) (hfiber : ∀ t, f t = f u → t ∈ interior S) :
    f u ∈ interior (f '' S) := by
  have hclosed : IsClosed (f '' (interior S)ᶜ) := hf _ isOpen_interior.isClosed_compl
  have hu : f u ∈ (f '' (interior S)ᶜ)ᶜ := by
    rintro ⟨t, ht, heq⟩
    exact ht (hfiber t heq)
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hu)
  intro y hy
  obtain ⟨t, rfl⟩ := hs y
  have ht : t ∈ interior S := by
    by_contra h
    exact hy ⟨t, h, rfl⟩
  exact ⟨t, interior_subset ht, rfl⟩

/-- A singleton fibre at an interior time of an interval maps to an interior
point of the interval image under a proper surjective curve. -/
theorem mem_interior_image_Icc_of_singleton_fiber
    {Y : Type*} [TopologicalSpace Y] (f : ℝ → Y)
    (hf : IsProperMap f) (hs : Surjective f) {a u b : ℝ}
    (hau : a < u) (hub : u < b) (hfiber : ∀ t, f t = f u → t = u) :
    f u ∈ interior (f '' Icc a b) := by
  apply mem_interior_image_of_fiber_subset_interior f hf.isClosedMap hs (Icc a b) u
  intro t ht
  rw [hfiber t ht, interior_Icc]
  exact ⟨hau, hub⟩

end LatticeProb

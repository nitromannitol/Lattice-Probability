import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Maps.Basic

/-! # Homeomorphisms induced by quotient maps -/

set_option autoImplicit false

open Function Topology

namespace LatticeProb

/-- Quotient maps with the same fibres induce a homeomorphism of their codomains. -/
theorem exists_homeomorph_of_quotient_maps_same_fibers
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : X → Z) (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfg : ∀ s t, f s = f t ↔ g s = g t) :
    ∃ e : Y ≃ₜ Z, ∀ x, e (f x) = g x := by
  classical
  let h : Y → Z := fun y => g (surjInv hf.surjective y)
  have hcomp : ∀ x, h (f x) = g x := by
    intro x
    apply (hfg _ _).mp
    exact surjInv_eq hf.surjective (f x)
  have hinj : Injective h := by
    intro y y' hy
    obtain ⟨x, rfl⟩ := hf.surjective y
    obtain ⟨x', rfl⟩ := hf.surjective y'
    apply (hfg x x').mpr
    simpa only [hcomp] using hy
  have hsurj : Surjective h := by
    intro z
    obtain ⟨x, rfl⟩ := hg.surjective z
    exact ⟨f x, hcomp x⟩
  let e : Y ≃ Z := Equiv.ofBijective h ⟨hinj, hsurj⟩
  have he : ∀ x, e (f x) = g x := hcomp
  have heinv : ∀ x, e.symm (g x) = f x := by
    intro x
    rw [← he x, e.symm_apply_apply]
  have hc : Continuous e := hf.continuous_iff.mpr (by
    simpa only [Function.comp_def, he] using hg.continuous)
  have hci : Continuous e.symm := hg.continuous_iff.mpr (by
    simpa only [Function.comp_def, heinv] using hf.continuous)
  exact ⟨⟨e, hc, hci⟩, he⟩

end LatticeProb

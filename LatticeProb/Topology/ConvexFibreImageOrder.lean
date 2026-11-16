import Mathlib.Order.Quotient
import Mathlib.Data.Setoid.Basic

/-! # The order induced by convex fibres -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A map with order-convex fibres induces a linear order on its range for which
its range restriction is monotone. -/
theorem exists_linearOrder_range_of_convex_fibres {A B : Type*} [LinearOrder A]
    (f : A → B)
    (hf : ∀ x y z, x ≤ y → y ≤ z → f x = f z → f y = f x) :
    ∃ ord : LinearOrder (range f), @Monotone A (range f) _ ord.toPreorder (fun x => (⟨f x, ⟨x, rfl⟩⟩ : range f)) := by
  classical
  let s : Setoid A := Setoid.ker f
  have hconv : ∀ q : Quotient s, OrdConnected (Quotient.mk s ⁻¹' {q}) := by
    intro q
    apply ordConnected_iff.mpr
    intro x hx z hz _ y hy
    have hxz : f x = f z := by
      exact @Quotient.exact A s x z (hx.trans hz.symm)
    have hyx : f y = f x := hf x y z hy.1 hy.2 hxz
    change Quotient.mk s y = q
    exact (Quotient.sound hyx).trans hx
  let : ∀ q : Quotient s, OrdConnected (Quotient.mk s ⁻¹' {q}) := hconv
  let rep : range f → Quotient s := fun y => Quotient.mk s (Classical.choose y.2)
  have hrep : Function.Injective rep := by
    intro x y h
    have hxy : f (Classical.choose x.2) = f (Classical.choose y.2) := Quotient.exact h
    apply Subtype.ext
    exact (Classical.choose_spec x.2).symm.trans (hxy.trans (Classical.choose_spec y.2))
  let ord : LinearOrder (range f) := LinearOrder.lift' rep hrep
  refine ⟨ord, ?_⟩
  intro x y hxy
  change rep (⟨f x, ⟨x, rfl⟩⟩ : range f) ≤ rep (⟨f y, ⟨y, rfl⟩⟩ : range f)
  have hx : rep (⟨f x, ⟨x, rfl⟩⟩ : range f) = Quotient.mk s x := by
    apply Quotient.sound
    exact Classical.choose_spec (⟨f x, ⟨x, rfl⟩⟩ : range f).2
  have hy : rep (⟨f y, ⟨y, rfl⟩⟩ : range f) = Quotient.mk s y := by
    apply Quotient.sound
    exact Classical.choose_spec (⟨f y, ⟨y, rfl⟩⟩ : range f).2
  rw [hx, hy]
  exact Quotient.mk_monotone hxy

end LatticeProb

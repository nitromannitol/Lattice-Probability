import LatticeProb.Topology.QuotientFiberHomeomorphism
import Mathlib.Topology.Separation.Hausdorff

/-! # Range homeomorphisms induced by maps from compact spaces -/

set_option autoImplicit false

open Function Set Topology

namespace LatticeProb

/-- Continuous maps on a compact space with equal fibres induce a homeomorphism
between their ranges that preserves the parameter. -/
theorem exists_range_homeomorph_of_compact_same_fibers
    {X Y Z : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : X → Y) (g : X → Z) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x y, f x = f y ↔ g x = g y) :
    ∃ e : range f ≃ₜ range g,
      ∀ x, e (rangeFactorization f x) = rangeFactorization g x := by
  apply exists_homeomorph_of_quotient_maps_same_fibers
    (rangeFactorization f) (rangeFactorization g)
    (IsQuotientMap.of_surjective_continuous rangeFactorization_surjective hf.rangeFactorization)
    (IsQuotientMap.of_surjective_continuous rangeFactorization_surjective hg.rangeFactorization)
  intro x y
  simpa only [Subtype.ext_iff, rangeFactorization] using hfg x y

end LatticeProb

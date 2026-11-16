import LatticeProb.Topology.ComplementComponents
import LatticeProb.Topology.EmbeddedDiskConnectedInterior

/-! # Bounded complementary components between planar sets -/

set_option autoImplicit false

open Set Bornology

namespace LatticeProb

/-- A preconnected middle interior contains every bounded complementary component when the
complement of the union is preconnected and unbounded. -/
theorem bounded_complement_components_eq_of_middle
    {X B : Set ℂ} (hX : IsClosed X)
    (hext : IsPreconnected (X ∪ B)ᶜ) (hext_unbounded : ¬ IsBounded (X ∪ B)ᶜ)
    (hB : IsPreconnected (interior B)) (hdis : Disjoint (interior B) X)
    {p q : ℂ} (hp : p ∈ Xᶜ) (hq : q ∈ Xᶜ)
    (hp_bound : IsBounded (connectedComponentIn Xᶜ p))
    (hq_bound : IsBounded (connectedComponentIn Xᶜ q)) :
    connectedComponentIn Xᶜ p = connectedComponentIn Xᶜ q := by
  have hcontain : ∀ {z : ℂ}, z ∈ Xᶜ → IsBounded (connectedComponentIn Xᶜ z) →
      connectedComponentIn Xᶜ z ⊆ interior B := by
    intro z hz hbound
    have hsub : connectedComponentIn Xᶜ z ⊆ B := by
      intro y hy
      by_contra hyB
      have hyX : y ∈ Xᶜ := connectedComponentIn_subset Xᶜ z hy
      have hyext : y ∈ (X ∪ B)ᶜ := by simpa only [mem_compl_iff, mem_union, not_or] using
        (show y ∉ X ∧ y ∉ B from ⟨hyX, hyB⟩)
      have hextsub : (X ∪ B)ᶜ ⊆ connectedComponentIn Xᶜ z :=
        by
          rw [connectedComponentIn_eq hy]
          exact hext.subset_connectedComponentIn hyext (by
          intro w hw
          exact fun hwX => hw (Or.inl hwX))
      exact hext_unbounded (hbound.subset hextsub)
    exact interior_maximal hsub hX.isOpen_compl.connectedComponentIn
  have hpB : p ∈ interior B := hcontain hp hp_bound (mem_connectedComponentIn hp)
  have hqB : q ∈ interior B := hcontain hq hq_bound (mem_connectedComponentIn hq)
  have hBsub : interior B ⊆ Xᶜ := by
    intro z hz hzX
    exact (disjoint_left.mp hdis) hz hzX
  have hBcomp : interior B ⊆ connectedComponentIn Xᶜ p :=
    hB.subset_connectedComponentIn hpB hBsub
  exact connectedComponentIn_eq (hBcomp hqB)

/-- For two closed planar sets separated by the interior of an embedded disk, at most one
complementary component of their union is bounded, provided the exterior of the full union is
preconnected and unbounded. -/
theorem bounded_complement_components_eq_of_embedded_middle_disk
    {A B C : Set ℂ} (hA : closure (interior A) = A)
    (hC : closure (interior C) = C)
    (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ B)
    (hext : IsPreconnected ((A ∪ C) ∪ B)ᶜ)
    (hext_unbounded : ¬ IsBounded ((A ∪ C) ∪ B)ᶜ)
    (hBA : Disjoint (interior B) (interior A))
    (hBC : Disjoint (interior B) (interior C))
    {p q : ℂ} (hp : p ∈ (A ∪ C)ᶜ) (hq : q ∈ (A ∪ C)ᶜ)
    (hp_bound : IsBounded (connectedComponentIn (A ∪ C)ᶜ p))
    (hq_bound : IsBounded (connectedComponentIn (A ∪ C)ᶜ q)) :
    connectedComponentIn (A ∪ C)ᶜ p = connectedComponentIn (A ∪ C)ᶜ q :=
  bounded_complement_components_eq_of_middle
    ((hA ▸ isClosed_closure).union (hC ▸ isClosed_closure)) hext hext_unbounded
    (isConnected_interior_of_homeomorph_closedDisk e).isPreconnected
    (disjoint_union_right.mpr ⟨hA ▸ hBA.closure_right isOpen_interior,
      hC ▸ hBC.closure_right isOpen_interior⟩) hp hq hp_bound hq_bound

end LatticeProb

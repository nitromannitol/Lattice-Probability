import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff

/-! # Directed intersections of compact connected sets -/

open Set Topology

namespace LatticeProb.Topology

/-- A decreasing directed intersection of compact preconnected sets is preconnected. -/
theorem isPreconnected_iInter_of_directed_isCompact
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X] [Nonempty ι]
    {K : ι → Set X} (hdir : Directed (· ⊇ ·) K)
    (hcompact : ∀ i, IsCompact (K i)) (hconn : ∀ i, IsPreconnected (K i)) :
    IsPreconnected (⋂ i, K i) := by
  classical
  intro u v hu hv hcover ⟨x, hx, hxu⟩ ⟨y, hy, hyv⟩
  by_contra hno
  let S : Set X := ⋂ i, K i
  have hSclosed : IsClosed S := isClosed_iInter fun i => (hcompact i).isClosed
  have hno' : Disjoint S (u ∩ v) := by
    apply disjoint_left.mpr
    intro z hz huv
    exact hno ⟨z, hz, huv⟩
  have hxv : x ∉ v := fun hxv => (disjoint_left.mp hno') hx ⟨hxu, hxv⟩
  have hyu : y ∉ u := fun hyu => (disjoint_left.mp hno') hy ⟨hyu, hyv⟩
  have hdisj : Disjoint (S \ v) (S \ u) := by
    apply disjoint_left.mpr
    intro z hz₁ hz₂
    rcases hcover hz₁.1 with hzu | hzv
    · exact hz₂.2 hzu
    · exact hz₁.2 hzv
  obtain ⟨U, V, hU, hV, hleft, hright, hUV⟩ :=
    normal_separation (hSclosed.sdiff hv) (hSclosed.sdiff hu) hdisj
  have hScov : S ⊆ U ∪ V := by
    intro z hz
    rcases hcover hz with hzu | hzv
    · exact Or.inl (hleft ⟨hz, fun hzv => (disjoint_left.mp hno') hz ⟨hzu, hzv⟩⟩)
    · exact Or.inr (hright ⟨hz, fun hzu => (disjoint_left.mp hno') hz ⟨hzu, hzv⟩⟩)
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact hdir hcompact
    ((hU.union hV).mem_nhdsSet.mpr hScov)
  obtain ⟨z, -, hzU, hzV⟩ := hconn i U V hU hV hi
    ⟨x, mem_iInter.mp hx i, hleft ⟨hx, hxv⟩⟩
    ⟨y, mem_iInter.mp hy i, hright ⟨hy, hyu⟩⟩
  exact (disjoint_left.mp hUV) hzU hzV

end LatticeProb.Topology

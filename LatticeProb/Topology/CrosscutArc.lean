import LatticeProb.Topology.CrosscutSeparation
import LatticeProb.Topology.ComplementComponents
import LatticeProb.Bonanno.MatedCRTHarmonic.Topology.PlanarCore

/-!
# Crosscuts of complementary domains: arcs and frontier bookkeeping

Let `K ⊆ ℂ` be a closed connected set with at least two points, `C` a connected component of `ℂ \ K`, and `γ` an arc
(a crosscut of `C`) with endpoints `a, b` on `γ` and `γ ∩ K ⊆ {a, b}`.

* `isPreconnected_compl_of_isArcSet`: the complement of an arc in the plane is connected (an arc separates no two
  points of its complement; Borsuk, Eilenberg).
* `frontier_diff_eq_frontier_diff_pair`: `frontier C \ γ = frontier C \ {a, b}`.
* `compl_diff_nonempty_of_inter_subset`: some point lies outside `C ∪ γ`.
* `not_isPreconnected_frontier_diff_pair_of_crosscut`: the crosscut separation theorem
  (`not_isPreconnected_frontier_diff_of_crosscut`) in this setting: if `C \ γ` is not connected, the components of
  `C \ γ` are locally finite at the frontier points of `C` off `{a, b}`, and no such point lies in the closures of two
  distinct components, then `frontier C \ {a, b}` is not connected.
-/

open Set
open scoped Topology

namespace LatticeProb.Topology

/-- The complement of an arc in the plane is preconnected: any two points off the arc are joined by a path
avoiding it. -/
theorem isPreconnected_compl_of_isArcSet {γ : Set ℂ} (hγ : QuantumZipper.CA.Topo.IsArcSet γ) :
    IsPreconnected γᶜ := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  have h := MatedCRTHarmonic.Topology.not_separates_of_isArcSet hγ hx hy
  simp only [MatedCRTHarmonic.Topology.Separates, not_forall, not_exists] at h
  obtain ⟨p, hp⟩ := h
  exact ⟨range p, range_subset_iff.2 hp, ⟨0, p.source⟩, ⟨1, p.target⟩,
    (isConnected_range p.continuous).isPreconnected⟩

variable {α : Type*} [TopologicalSpace α]

/-- If the frontier of `C` lies in `K`, the points `a, b` lie on `γ`, and `γ` meets `K` only in `{a, b}`, then removing
`γ` from the frontier of `C` removes exactly `a` and `b`. -/
theorem frontier_diff_eq_frontier_diff_pair {K C γ : Set α} {a b : α} (hF : frontier C ⊆ K) (ha : a ∈ γ)
    (hb : b ∈ γ) (hγK : γ ∩ K ⊆ {a, b}) : frontier C \ γ = frontier C \ {a, b} := by
  ext x
  constructor
  · rintro ⟨hx, hxγ⟩
    refine ⟨hx, ?_⟩
    rintro (rfl | rfl)
    · exact hxγ ha
    · exact hxγ hb
  · rintro ⟨hx, hxab⟩
    exact ⟨hx, fun hxγ => hxab (hγK ⟨hxγ, hF hx⟩)⟩

/-- If `K` is a preconnected set with two points in a T1 space, disjoint from `C`, and `γ` meets `K` only in
`{a, b}`, then some point lies outside `C ∪ γ`: a nontrivial preconnected T1 set is infinite. -/
theorem compl_diff_nonempty_of_inter_subset [T1Space α] {K C γ : Set α} {a b : α} (hK : IsPreconnected K)
    (hKn : K.Nontrivial) (hCK : Disjoint C K) (hγK : γ ∩ K ⊆ {a, b}) : (Cᶜ \ γ).Nonempty := by
  obtain ⟨x, hxK, hxab⟩ :=
    ((hK.infinite_of_nontrivial hKn).sdiff ((finite_singleton b).insert a)).nonempty
  exact ⟨x, fun hxC => hCK.ne_of_mem hxC hxK rfl, fun hxγ => hxab (hγK ⟨hxγ, hxK⟩)⟩

/-- **A crosscut separates the frontier of a complementary domain.** Let `K ⊆ ℂ` be closed, preconnected and
nontrivial, `C` a connected component of `ℂ \ K`, and `γ` an arc containing `a, b` with `γ ∩ K ⊆ {a, b}`. If `C \ γ`
is not preconnected, the components of `C \ γ` are locally finite at the points of `frontier C \ γ`, and no such point
lies in the closures of two distinct components of `C \ γ`, then `frontier C \ {a, b}` is not preconnected. -/
theorem not_isPreconnected_frontier_diff_pair_of_crosscut {K C γ : Set ℂ} {a b : ℂ} (hK : IsClosed K)
    (hKc : IsPreconnected K) (hKn : K.Nontrivial) (hC : C ∈ connectedComponentsIn Kᶜ)
    (hγ : QuantumZipper.CA.Topo.IsArcSet γ) (ha : a ∈ γ) (hb : b ∈ γ) (hγK : γ ∩ K ⊆ {a, b})
    (hsep : ¬ IsPreconnected (C \ γ))
    (hkey : ∀ x ∈ frontier C \ γ, ∀ U ∈ connectedComponentsIn (C \ γ),
      ∀ V ∈ connectedComponentsIn (C \ γ), x ∈ closure U → x ∈ closure V → U = V)
    (hfin : ∀ x ∈ frontier C \ γ, ∃ N ∈ 𝓝 x,
      {U ∈ connectedComponentsIn (C \ γ) | (U ∩ N).Nonempty}.Finite) :
    ¬ IsPreconnected (frontier C \ {a, b}) := by
  rw [← frontier_diff_eq_frontier_diff_pair (frontier_subset_of_mem_connectedComponentsIn_compl hK hC) ha hb hγK]
  exact not_isPreconnected_frontier_diff_of_crosscut (isOpen_of_mem_connectedComponentsIn_compl hK hC)
    (QuantumZipper.CA.Topo.IsArcSet.isCompact hγ).isClosed (isPreconnected_compl_of_isArcSet hγ)
    (compl_diff_nonempty_of_inter_subset hKc hKn
      (subset_compl_iff_disjoint_right.1 (subset_of_mem_connectedComponentsIn hC)) hγK)
    hsep hkey hfin

end LatticeProb.Topology

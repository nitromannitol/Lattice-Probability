import LatticeProb.Topology.Unicoherence
import LatticeProb.Topology.ConnectedThickening

/-! # Connected plane domains from exterior barriers -/

open Set Bornology

namespace LatticeProb.Topology

/-- A closed connected unbounded barrier surrounding the complement of a prescribed set
produces a connected open domain with an unbounded connected complement. -/
theorem exists_domain_of_exterior_barrier {E N V : Set ℂ}
    (hE : IsClosed E) (hEc : IsConnected E) (hEu : ¬ IsBounded E)
    (hN : IsConnected N) (hNE : Disjoint N E) (hV : Vᶜ ⊆ E) :
    ∃ U : Set ℂ, N ⊆ U ∧ U ⊆ V ∧ IsOpen U ∧ IsConnected U ∧
      IsPreconnected Uᶜ ∧ ¬ IsBounded Uᶜ ∧
      ∀ a ∉ U, ¬ IsBounded (connectedComponentIn Uᶜ a) := by
  obtain ⟨x, hx⟩ := hN.nonempty
  have hNE' : N ⊆ Eᶜ := disjoint_left.mp hNE
  have hxE : x ∈ Eᶜ := hNE' hx
  let U := connectedComponentIn Eᶜ x
  have hNU : N ⊆ U := hN.isPreconnected.subset_connectedComponentIn hx hNE'
  have hUE : U ⊆ Eᶜ := connectedComponentIn_subset _ _
  have hEU : E ⊆ Uᶜ := fun _ he hu => hUE hu he
  have hUc : IsPreconnected Uᶜ :=
    isPreconnected_compl_of_mem_connectedComponentsIn_compl hE hEc.isPreconnected hEc.nonempty
      ⟨x, hxE, rfl⟩
  have hUu : ¬ IsBounded Uᶜ := fun h => hEu (h.subset hEU)
  refine ⟨U, hNU, ?_, hE.isOpen_compl.connectedComponentIn,
    ⟨⟨x, hNU hx⟩, isPreconnected_connectedComponentIn⟩, hUc, hUu, ?_⟩
  · intro y hy
    by_contra hyV
    exact hUE hy (hV hyV)
  · intro a ha hb
    apply hUu
    apply hb.subset
    exact hUc.subset_connectedComponentIn ha (Subset.rfl)

/-- A compact continuum has a connected open neighborhood inside any given exterior barrier. -/
theorem exists_domain_of_compact_exterior_barrier {K E V : Set ℂ}
    (hK : IsCompact K) (hKc : IsConnected K) (hE : IsClosed E)
    (hEc : IsConnected E) (hEu : ¬ IsBounded E) (hKE : Disjoint K E)
    (hV : Vᶜ ⊆ E) :
    ∃ U : Set ℂ, K ⊆ U ∧ U ⊆ V ∧ IsOpen U ∧ IsConnected U ∧
      IsPreconnected Uᶜ ∧ ¬ IsBounded Uᶜ ∧
      ∀ a ∉ U, ¬ IsBounded (connectedComponentIn Uᶜ a) := by
  have hKE' : K ⊆ Eᶜ := disjoint_left.mp hKE
  obtain ⟨r, hr, hrE⟩ := hK.exists_thickening_subset_open hE.isOpen_compl hKE'
  obtain ⟨U, hNU, hUV, hUo, hUc, hcc, hcu, hcomp⟩ :=
    exists_domain_of_exterior_barrier hE hEc hEu (isConnected_thickening hKc hr)
      (disjoint_left.mpr hrE) hV
  exact ⟨U, (Metric.self_subset_thickening hr K).trans hNU, hUV, hUo, hUc, hcc, hcu, hcomp⟩

end LatticeProb.Topology

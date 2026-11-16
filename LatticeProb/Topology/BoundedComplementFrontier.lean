import LatticeProb.Topology.Unicoherence
import LatticeProb.Topology.EmbeddedClosedDiskExterior

/-! # Boundaries of bounded complementary components -/

open Set Metric Bornology

namespace LatticeProb.Topology

/-- A bounded complementary component whose boundary lies in a union meets the first set
on its boundary when the complement of the second set is preconnected and unbounded. -/
theorem frontier_inter_nonempty_of_compl_preconnected {A B U : Set ℂ}
    (hUo : IsOpen U) (hUne : U.Nonempty) (hUb : IsBounded U)
    (hUsub : U ⊆ Bᶜ) (hfr : frontier U ⊆ A ∪ B)
    (hBc : IsPreconnected Bᶜ) (hBu : ¬ IsBounded Bᶜ) :
    (frontier U ∩ A).Nonempty := by
  by_contra h
  have hfrB : frontier U ⊆ B := by
    intro x hx
    rcases hfr hx with hxA | hxB
    · exact False.elim (h ⟨x, hx, hxA⟩)
    · exact hxB
  have hsub : Bᶜ ⊆ U := by
    apply hBc.subset_of_closure_inter_subset hUo
    · obtain ⟨x, hx⟩ := hUne
      exact ⟨x, hUsub hx, hx⟩
    · intro x hx
      by_contra hxU
      have hxfr : x ∈ frontier U := by
        rw [hUo.frontier_eq]
        exact ⟨hx.1, hxU⟩
      exact hx.2 (hfrB hxfr)
  exact hBu (hUb.subset hsub)

/-- The frontier of a bounded component of a union complement meets both sets if each set
has a preconnected, unbounded complement. -/
theorem frontier_inter_nonempty_of_bounded_compl_component {A B U : Set ℂ}
    (hA : IsClosed A) (hB : IsClosed B)
    (hAc : IsPreconnected Aᶜ) (hAu : ¬ IsBounded Aᶜ)
    (hBc : IsPreconnected Bᶜ) (hBu : ¬ IsBounded Bᶜ)
    (hU : U ∈ connectedComponentsIn (A ∪ B)ᶜ) (hUb : IsBounded U) :
    (frontier U ∩ A).Nonempty ∧ (frontier U ∩ B).Nonempty := by
  have hUo := isOpen_of_mem_connectedComponentsIn_compl (hA.union hB) hU
  have hUne := (isConnected_of_mem_connectedComponentsIn hU).nonempty
  have hUs := subset_of_mem_connectedComponentsIn hU
  have hfr := frontier_subset_of_mem_connectedComponentsIn_compl (hA.union hB) hU
  constructor
  · apply frontier_inter_nonempty_of_compl_preconnected hUo hUne hUb _ hfr hBc hBu
    intro x hx hxB
    exact hUs hx (Or.inr hxB)
  · apply frontier_inter_nonempty_of_compl_preconnected hUo hUne hUb _ _ hAc hAu
    · intro x hx hxA
      exact hUs hx (Or.inl hxA)
    · simpa only [union_comm] using hfr

/-- A bounded complementary component of a connected union has a frontier point in
both closed sets, provided both individual complements are preconnected and unbounded. -/
theorem frontier_inter_inter_nonempty_of_bounded_compl_component {A B U : Set ℂ}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : IsConnected (A ∪ B))
    (hAc : IsPreconnected Aᶜ) (hAu : ¬ IsBounded Aᶜ)
    (hBc : IsPreconnected Bᶜ) (hBu : ¬ IsBounded Bᶜ)
    (hU : U ∈ connectedComponentsIn (A ∪ B)ᶜ) (hUb : IsBounded U) :
    (frontier U ∩ (A ∩ B)).Nonempty := by
  have hfront := isConnected_frontier_of_mem_connectedComponentsIn_compl (hA.union hB) hAB hU
  obtain ⟨hleft, hright⟩ :=
    frontier_inter_nonempty_of_bounded_compl_component hA hB hAc hAu hBc hBu hU hUb
  exact isPreconnected_closed_iff.mp hfront.isPreconnected A B hA hB
    (frontier_subset_of_mem_connectedComponentsIn_compl (hA.union hB) hU) hleft hright

/-- Every bounded complementary component of two embedded disks has boundary points in both. -/
theorem frontier_inter_nonempty_of_embedded_disks {A B U : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hU : U ∈ connectedComponentsIn (A ∪ B)ᶜ) (hUb : IsBounded U) :
    (frontier U ∩ A).Nonempty ∧ (frontier U ∩ B).Nonempty := by
  have hdisk (D : Set ℂ) (e : closedBall (0 : ℂ) 1 ≃ₜ D) : IsClosed D := by
    have h : IsCompact (range (fun x => (e x : ℂ))) :=
      isCompact_range (continuous_subtype_val.comp e.continuous)
    have hr : range (fun x => (e x : ℂ)) = D := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).2
      · intro hy
        exact ⟨e.symm ⟨y, hy⟩, by simp⟩
    rw [hr] at h
    exact h.isClosed
  obtain ⟨hAc, hAu⟩ := LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded eA
  obtain ⟨hBc, hBu⟩ := LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded eB
  exact frontier_inter_nonempty_of_bounded_compl_component (hdisk A eA) (hdisk B eB)
    hAc hAu hBc hBu hU hUb

/-- If two embedded disks meet, each bounded complementary component has a frontier point
in their intersection. -/
theorem frontier_inter_inter_nonempty_of_embedded_disks {A B U : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hAB : (A ∩ B).Nonempty) (hU : U ∈ connectedComponentsIn (A ∪ B)ᶜ)
    (hUb : IsBounded U) : (frontier U ∩ (A ∩ B)).Nonempty := by
  have hdisk (D : Set ℂ) (e : closedBall (0 : ℂ) 1 ≃ₜ D) :
      IsClosed D ∧ IsConnected D := by
    let : CompactSpace D := e.compactSpace
    let : ConnectedSpace (closedBall (0 : ℂ) 1) :=
      isConnected_iff_connectedSpace.mp (Metric.isConnected_closedBall (by norm_num))
    let : ConnectedSpace D := e.connectedSpace_iff.mp inferInstance
    exact ⟨(isCompact_iff_compactSpace.mpr inferInstance).isClosed,
      isConnected_iff_connectedSpace.mpr inferInstance⟩
  obtain ⟨hA, hAc⟩ := hdisk A eA
  obtain ⟨hB, hBc⟩ := hdisk B eB
  obtain ⟨hAcp, hAu⟩ := LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded eA
  obtain ⟨hBcp, hBu⟩ := LatticeProb.complex_embedded_closed_disk_compl_preconnected_unbounded eB
  exact frontier_inter_inter_nonempty_of_bounded_compl_component hA hB (hAc.union hAB hBc)
    hAcp hAu hBcp hBu hU hUb

end LatticeProb.Topology

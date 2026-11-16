import LatticeProb.Topology.ConnectedThickening
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Complex.Basic

/-! Compact connected neighborhoods inside open connected sets. -/

open Set Metric Bornology

namespace LatticeProb.Topology

theorem exists_compact_connected_superset {O S : Set ℂ} {p : ℂ}
    (hO : IsOpen O) (hOc : IsConnected O) (hp : p ∈ O)
    (hS : IsCompact S) (hSO : S ⊆ O) :
    ∃ T : Set ℂ, IsCompact T ∧ IsConnected T ∧ S ⊆ T ∧ p ∈ T ∧ T ⊆ O := by
  classical
  let : LocallyPathConnectedSpace ℂ := LocallyPathConnectedSpace.of_bases
    (fun x => Metric.nhds_basis_ball) (fun x r hr =>
      (convex_ball x r).isPathConnected ⟨x, mem_ball_self hr⟩)
  have hpaths : ∀ x : S, ∃ T : Set ℂ, IsOpen T ∧ x.1 ∈ T ∧
      IsCompact (closure T) ∧ IsConnected (closure T) ∧ p ∈ closure T ∧ closure T ⊆ O := by
    intro x
    obtain ⟨γ, hγ⟩ := (hO.isConnected_iff_isPathConnected.mp hOc).joinedIn p hp x (hSO x.2)
    let P : Set ℂ := range γ
    have hPc : IsCompact P := isCompact_range γ.continuous
    have hPn : IsConnected P := isConnected_range γ.continuous
    have hPO : P ⊆ O := by rintro _ ⟨t, rfl⟩; exact hγ t
    obtain ⟨r, hr, hrO⟩ := hPc.exists_cthickening_subset_open hO hPO
    let T := thickening r P
    have hPT : P ⊆ T := self_subset_thickening hr P
    have hTC : closure T ⊆ O := (closure_thickening_subset_cthickening r P).trans hrO
    have hpP : p ∈ P := ⟨0, γ.source⟩
    have hxP : x.1 ∈ P := ⟨1, γ.target⟩
    exact ⟨T, isOpen_thickening, hPT hxP, hPc.isBounded.thickening.isCompact_closure,
      (isConnected_thickening hPn hr).closure, subset_closure (hPT hpP), hTC⟩
  choose T hTo hxT hTc hTconn hpT hTO using hpaths
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover T hTo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxT ⟨x, hx⟩⟩)
  let C := ⋃ x ∈ s, closure (T x)
  have hCc : IsCompact C := s.isCompact_biUnion (fun x _ => hTc x)
  refine ⟨{p} ∪ C, isCompact_singleton.union hCc, ?_, ?_, Or.inl rfl, ?_⟩
  · refine ⟨⟨p, Or.inl rfl⟩, isPreconnected_of_forall p ?_⟩
    intro y hy
    rcases hy with hy | hy
    · subst y
      exact ⟨{p}, subset_union_left, rfl, rfl, isPreconnected_singleton⟩
    · obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
      refine ⟨closure (T i), ?_, hpT i, hyi, (hTconn i).isPreconnected⟩
      intro z hz
      exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hz⟩⟩)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact Or.inr (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, subset_closure hxi⟩⟩)
  · rintro x (rfl | hx)
    · exact hp
    · obtain ⟨i, _, hxi⟩ := mem_iUnion₂.mp hx
      exact hTO i hxi

end LatticeProb.Topology

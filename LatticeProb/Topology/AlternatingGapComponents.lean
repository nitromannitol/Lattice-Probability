import LatticeProb.Topology.ExteriorChartBoundary
import LatticeProb.Topology.EmbeddedDiskContactChord

/-! # Separation of alternating accessible gaps -/

open Set Metric Complex

namespace LatticeProb.Topology

/-- Accessible boundary points separated by two alternating disk contacts belong to
    distinct components of the complement of the two disks. -/
theorem alternating_access_points_not_same_component {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B))
    (g : closure Aᶜ → ℂ) (hg : Continuous g) (hgi : Function.Injective g)
    (hgd : ∀ x, g x ∈ closedBall (0 : ℂ) 1)
    (f : ℝ → frontier A)
    (hgf : ∀ t, g ⟨f t, by
      exact (show (f t : ℂ) ∈ closure A ∩ closure Aᶜ from
        (frontier_eq_closure_inter_closure (s := A)) ▸ (f t).property).2⟩ = circleMap 0 1 t)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hda : d < a + 2 * Real.pi)
    (hb : (f b : ℂ) ∈ A ∩ B) (hd : (f d : ℂ) ∈ A ∩ B)
    (hbd : (f b : ℂ) ≠ f d)
    {p q : ℂ} {P Q : Set ℂ}
    (hp : p ∈ (A ∪ B)ᶜ) (hq : q ∈ (A ∪ B)ᶜ)
    (hPc : IsCompact P) (hQc : IsCompact Q)
    (hPconn : IsConnected P) (hQconn : IsConnected Q)
    (haP : (f a : ℂ) ∈ P) (hpP : p ∈ P)
    (hcQ : (f c : ℂ) ∈ Q) (hqQ : q ∈ Q)
    (hPS : P ⊆ Bᶜ ∩ closure Aᶜ) (hQS : Q ⊆ Bᶜ ∩ closure Aᶜ) :
    connectedComponentIn (A ∪ B)ᶜ p ≠ connectedComponentIn (A ∪ B)ᶜ q := by
  intro heq
  have hA : IsClosed A := (LatticeProb.closure_interior_of_homeomorph_closedDisk eA) ▸ isClosed_closure
  have hB : IsClosed B := (LatticeProb.closure_interior_of_homeomorph_closedDisk eB) ▸ isClosed_closure
  have hqcomp : q ∈ connectedComponentIn (A ∪ B)ᶜ p := by
    rw [heq]
    exact mem_connectedComponentIn hq
  have hUS : (A ∪ B)ᶜ ⊆ Bᶜ ∩ closure Aᶜ := by
    intro x hx
    exact ⟨fun hxB => hx (Or.inr hxB), subset_closure (fun hxA => hx (Or.inl hxA))⟩
  obtain ⟨T, hTc, hTconn, hTcontains, hTS⟩ :=
    exists_compact_connected_join_of_component (hA.union hB).isOpen_compl hp hqcomp
      hPS hQS hUS hPc hQc hPconn hQconn hpP hqQ
  obtain ⟨R, hRc, hRconn, hbR, hdR, hRS, _⟩ :=
    exists_contact_chord_of_embedded_disks eA eB hdis hb hd hbd
  classical
  let G : ℂ → ℂ := fun x => if hx : x ∈ closure Aᶜ then g ⟨x, hx⟩ else 0
  have hG (x : closure Aᶜ) : G x = g x := by
    change (if hx : (x : ℂ) ∈ closure Aᶜ then g ⟨x, hx⟩ else 0) = g x
    rw [dite_eq_left x.property]
  have hGc : ContinuousOn G (closure Aᶜ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (closure Aᶜ).domRestrict G = g := funext hG
    rw [he]
    exact hg
  have hGi : InjOn G (closure Aᶜ) := by
    intro x hx y hy hxy
    have : g ⟨x, hx⟩ = g ⟨y, hy⟩ := by simpa only [← hG] using hxy
    exact congrArg Subtype.val (hgi this)
  have hGf (t : ℝ) : G (f t) = exp (t * I) := by
    have h := hgf t
    rw [← hG] at h
    simpa [circleMap] using h
  have hTsub : T ⊆ closure Aᶜ := fun x hx => (hTS hx).2
  have hRsub : R ⊆ closure Aᶜ := fun x hx => (hRS hx).2
  have hTD : G '' T ⊆ closedBall (0 : ℂ) 1 := by
    rintro z ⟨x, hx, rfl⟩
    rw [hG ⟨x, hTsub hx⟩]
    exact hgd _
  have hRD : G '' R ⊆ closedBall (0 : ℂ) 1 := by
    rintro z ⟨x, hx, rfl⟩
    rw [hG ⟨x, hRsub hx⟩]
    exact hgd _
  have hinter := nonempty_inter_of_alternating_disk_chart_on hGc hGi hTsub hRsub
    hTc hTconn hRc hRconn hTD hRD hab hbc hcd hda
    ⟨f a, hTcontains (Or.inl haP), hGf a⟩
    ⟨f c, hTcontains (Or.inr hcQ), hGf c⟩
    ⟨f b, hbR, hGf b⟩ ⟨f d, hdR, hGf d⟩
  obtain ⟨x, hxT, hxR⟩ := hinter
  exact (hTS hxT).1 (hRS hxR).1

end LatticeProb.Topology

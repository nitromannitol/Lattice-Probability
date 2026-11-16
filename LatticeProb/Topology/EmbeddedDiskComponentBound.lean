import LatticeProb.Topology.AlternatingGapComponents
import LatticeProb.Topology.ThreeComplementComponents

/-! # Components of the intersection of embedded disks -/

open Set Metric Complex

namespace LatticeProb.Topology

/-- Three distinct contact components yield three distinct complementary components. -/
theorem three_contact_components_give_three_compl_components {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B))
    {x y z : ℂ} (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (hz : z ∈ A ∩ B)
    (hxy : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) y)
    (hxz : connectedComponentIn (A ∩ B) x ≠ connectedComponentIn (A ∩ B) z)
    (hyz : connectedComponentIn (A ∩ B) y ≠ connectedComponentIn (A ∩ B) z) :
    ∃ p q r : ℂ, p ∈ (A ∪ B)ᶜ ∧ q ∈ (A ∪ B)ᶜ ∧ r ∈ (A ∪ B)ᶜ ∧
      connectedComponentIn (A ∪ B)ᶜ p ≠ connectedComponentIn (A ∪ B)ᶜ q ∧
      connectedComponentIn (A ∪ B)ᶜ p ≠ connectedComponentIn (A ∪ B)ᶜ r ∧
      connectedComponentIn (A ∪ B)ᶜ q ≠ connectedComponentIn (A ∪ B)ᶜ r := by
  obtain ⟨g, f, hg, hgi, hgd, hgf, a, b, c, hab, hbc, hca, ha, hb, hc,
    hba, hcb, hac, t₁, ht₁, t₂, ht₂, t₃, ht₃, hgap⟩ :=
      exists_chart_ordered_contacts_and_accessible_gaps eA eB hdis hx hy hz hxy hxz hyz
  have hperiod (t : ℝ) : f (t + 2 * Real.pi) = f t := by
    apply Subtype.ext
    have he : g ⟨f (t + 2 * Real.pi), by
      exact (show (f (t + 2 * Real.pi) : ℂ) ∈ closure A ∩ closure Aᶜ from
        (frontier_eq_closure_inter_closure (s := A)) ▸ (f (t + 2 * Real.pi)).property).2⟩ =
      g ⟨f t, by
        exact (show (f t : ℂ) ∈ closure A ∩ closure Aᶜ from
          (frontier_eq_closure_inter_closure (s := A)) ▸ (f t).property).2⟩ := by
      rw [hgf, hgf, periodic_circleMap]
    exact congrArg (fun v : closure Aᶜ => (v : ℂ)) (hgi he)
  have hbcne : (f b : ℂ) ≠ f c := by
    intro h
    exact hcb (h ▸ mem_connectedComponentIn hb)
  have hban : (f b : ℂ) ≠ f a := by
    intro h
    apply hba
    rw [h]
    exact mem_connectedComponentIn ha
  have hcbn : (f c : ℂ) ≠ f b := hbcne.symm
  obtain ⟨p, P, hp, hPc, hPconn, ht₁P, hpP, hPS⟩ := hgap t₁ (by simp)
  obtain ⟨q, Q, hq, hQc, hQconn, ht₂Q, hqQ, hQS⟩ := hgap t₂ (by simp)
  obtain ⟨r, R, hr, hRc, hRconn, ht₃R, hrR, hRS⟩ := hgap t₃ (by simp)
  have hpq := alternating_access_points_not_same_component eA eB hdis g hg hgi hgd f hgf
    ht₁.2 ht₂.1 ht₂.2 (by linarith [ht₁.1]) hb hc hbcne hp hq
    hPc hQc hPconn hQconn ht₁P hpP ht₂Q hqQ hPS hQS
  have hpr := alternating_access_points_not_same_component (a := t₁) (b := b) (c := t₃) (d := a + 2 * Real.pi) eA eB hdis g hg hgi hgd f hgf
    ht₁.2 (lt_trans ht₂.1 (lt_trans ht₂.2 ht₃.1)) ht₃.2 (by linarith [ht₁.1])
    hb (by simpa only [hperiod] using ha) (by simpa only [hperiod] using hban) hp hr
    hPc hRc hPconn hRconn ht₁P hpP ht₃R hrR hPS hRS
  have hqr := alternating_access_points_not_same_component (a := t₂) (b := c) (c := t₃) (d := b + 2 * Real.pi) eA eB hdis g hg hgi hgd f hgf
    ht₂.2 ht₃.1 (by linarith [ht₃.2, hab]) (by linarith [ht₂.1])
    hc (by simpa only [hperiod] using hb) (by simpa only [hperiod] using hcbn) hq hr
    hQc hRc hQconn hRconn ht₂Q hqQ ht₃R hrR hQS hRS
  exact ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩

/-- If the union has at most one bounded complementary component, two embedded
closed disks with disjoint interiors meet in at most two components. -/
theorem cardinal_inter_components_le_two_of_embedded_disks {A B : Set ℂ}
    (eA : closedBall (0 : ℂ) 1 ≃ₜ A) (eB : closedBall (0 : ℂ) 1 ≃ₜ B)
    (hdis : Disjoint (interior A) (interior B))
    [Subsingleton (BoundedPlaneComplementComponent (A ∪ B))] :
    Cardinal.mk (ConnectedComponents ↥(A ∩ B)) ≤ 2 := by
  classical
  have hA : IsCompact A := by
    let : CompactSpace A := eA.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hB : IsCompact B := by
    let : CompactSpace B := eB.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  by_contra h
  have hn : (3 : Cardinal) ≤ Cardinal.mk (ConnectedComponents ↥(A ∩ B)) := by
    have := Cardinal.natCast_add_one_le_iff.mpr (lt_of_not_ge h)
    norm_num at this ⊢
    exact this
  obtain ⟨s, hs⟩ := Cardinal.exists_finset_eq_card hn
  let e : Fin 3 ≃ s := (s.equivFinOfCardEq hs.symm).symm
  let y : Fin 3 → ConnectedComponents ↥(A ∩ B) := fun i => (e i).val
  let x : Fin 3 → ↥(A ∩ B) := fun i => Classical.choose (ConnectedComponents.surjective_coe (y i))
  have hinj : Function.Injective (fun i => ConnectedComponents.mk (x i)) := by
    intro i j hij
    have heq : y i = y j := by
      simpa [x, Classical.choose_spec (ConnectedComponents.surjective_coe (y i)),
        Classical.choose_spec (ConnectedComponents.surjective_coe (y j))] using hij
    exact e.injective (Subtype.ext heq)
  have hne (i j : Fin 3) (hij : i ≠ j) :
      connectedComponentIn (A ∩ B) (x i) ≠ connectedComponentIn (A ∩ B) (x j) := by
    intro heq
    apply hij
    apply hinj
    rw [ConnectedComponents.coe_eq_coe, ← Subtype.val_injective.image_injective.eq_iff,
      ← connectedComponentIn_eq_image (x i).property,
      ← connectedComponentIn_eq_image (x j).property]
    exact heq
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
    three_contact_components_give_three_compl_components eA eB hdis
      (x 0).property (x 1).property (x 2).property
      (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
  rcases two_of_three_compl_components_eq (hA.union hB) hp hq hr with h | h | h
  · exact hpq h
  · exact hpr h
  · exact hqr h

end LatticeProb.Topology

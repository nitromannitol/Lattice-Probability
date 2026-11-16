import LatticeProb.Probability.Percolation.JoinedCrossingReflection

/-!
# Orientation transfer for joined crossings

A horizontal crossing of a square intersects a vertical crossing. Consequently, if the
vertical crossing is joined to a target in a larger region, so is the horizontal crossing.
-/

open Percolation.Literature

namespace EdgeCrossing

private abbrev Site := LatticeModels.Site 2

/-- A horizontal crossing and a joined vertical crossing yield a joined horizontal crossing. -/
theorem horizontal_joined_of_vertical_joined (n : ℕ) (R : Finset Site) (T : Set Site)
    (hSR : (rectangle n n : Set Site) ⊆ R)
    {η : (LatticeModels.zdGraph 2).edgeSet → Prop}
    (hH : η ∈ crossingIn (rectangle n n) (leftSide n n) (rightSide n n))
    (hV : η ∈ joinedCrossingIn (rectangle n n) R (bottomSide n n) (topSide n n) T) :
    η ∈ joinedCrossingIn (rectangle n n) R (leftSide n n) (rightSide n n) T := by
  let ω := extend (LatticeModels.zdGraph 2) η
  change ω ∈ openCrossing _ _ _ at hH
  change ω ∈ joinedCrossing _ _ _ _ _ at hV ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := hH
  obtain ⟨c, hc, d, hd, t, ht, hcd, hct⟩ := hV
  have hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet := extend_subset _ _
  obtain ⟨P, hPS, hPω⟩ := exists_walk_of_mem_openConnIn hω hab
  obtain ⟨Q, hQS, hQω⟩ := exists_walk_of_mem_openConnIn hω hcd
  have hbox : ∀ {x y : Site} (W : (LatticeModels.zdGraph 2).Walk x y),
      (∀ z ∈ W.support, z ∈ (rectangle n n : Finset Site)) →
      ∀ z ∈ W.support, (0 : ℤ) ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro x y W h z hz
    exact mem_rectangle_iff.mp (h z hz)
  have ha' := ha
  have hb' := hb
  simp only [Finset.mem_coe, leftSide, rightSide, bottomSide, topSide,
    Finset.mem_filter] at ha' hb' hc hd
  obtain ⟨u, huP, huQ⟩ := exists_mem_support_of_crossing P Q
    (hbox P hPS) (hbox Q hQS) ha'.2 hb'.2 hc.2 hd.2
  have hau : ω ∈ openConnIn R a u := openConnIn_mono hSR _ _
    (mem_openConnIn_of_mem_support P hPS hPω huP)
  have huc : ω ∈ openConnIn R u c := openConnIn_mono hSR _ _ (by
    rw [openConnIn_comm]
    exact mem_openConnIn_of_mem_support Q hQS hQω huQ)
  exact ⟨a, ha, b, hb, t, ht, hab,
    PlanarDuality.openConnIn_trans (PlanarDuality.openConnIn_trans hau huc) hct⟩

end EdgeCrossing

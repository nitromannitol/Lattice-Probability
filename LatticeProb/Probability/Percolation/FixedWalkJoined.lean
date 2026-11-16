import LatticeProb.Probability.Percolation.FixedBoundaryWalk
import LatticeProb.Probability.Percolation.VerticalJoinedExposure

/-!
# Joining a fixed boundary walk to first contact

An open vertical walk and an open path from the outer left boundary to that walk
form a joined crossing in the same configuration.
-/

open Percolation.Literature SimpleGraph

noncomputable section

namespace EdgeCrossing

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

/-- A fixed walk open throughout an exposure cell joins its first-contact path. -/
theorem verticalExposureCell_inter_firstContact_subset_joined (n : ℕ)
    (D : Finset V) {c d : V} (Q : G.Walk c d)
    (hc : c 1 = 0) (hd : d 1 = n)
    (hQ : ∀ z ∈ Q.support, z ∈ rectangle n n)
    (hopen : ∀ η ∈ verticalExposureCell n D, ∀ x y, s(x, y) ∈ Q.edges →
      s(exposureRotation n x, exposureRotation n y) ∈
        BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv) (extend G η)) :
    verticalExposureCell n D ∩ firstContact n Q (!true) ⊆
      joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n) := by
  intro η hη
  have hSR : (rectangle n n : Set V) ⊆ centeredSquare n := by
    intro z hz
    rw [Finset.mem_coe, centeredSquare, mem_centered_square]
    simp only [Finset.mem_coe, mem_rectangle_iff] at hz
    omega
  apply (mem_joinedCrossingIn_iff_walk _ _ _ _ _ hSR η).mpr
  have hc' : c ∈ bottomSide n n := by
    simp only [bottomSide, Finset.mem_filter]
    exact ⟨hQ c Q.start_mem_support, hc⟩
  have hd' : d ∈ topSide n n := by
    simp only [topSide, Finset.mem_filter]
    exact ⟨hQ d Q.end_mem_support, hd⟩
  have hQopen : ∀ e ∈ Q.edges, e ∈ extend G η := by
    intro e he
    obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e
    have h := hopen η hη.1 x y he
    change sym2Equiv (exposureRotation n).toEquiv s(x, y) ∈
      BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv) (extend G η) at h
    rw [BondConfig.mem_relabel_iff, Equiv.symm_apply_apply] at h
    exact h
  have hcontact := hη.2
  change extend G η ∈ avoidingPath (centeredSquare n)
    {z | z ∈ Q.support ∨ reflY 0 z ∈ Q.support}
    {z | z ∈ Q.support} (outerLeft n) at hcontact
  obtain ⟨t, ht, v, hv, P, hP, _, hPopen⟩ := hcontact
  refine ⟨c, hc', d, hd', Q, hQ, hQopen, v, hv, t, ht, ?_⟩
  rw [openConnIn_comm]
  exact mem_openConnIn_of_walk P hP hPopen

end EdgeCrossing

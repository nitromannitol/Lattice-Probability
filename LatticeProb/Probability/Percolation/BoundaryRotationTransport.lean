import LatticeProb.Probability.Percolation.VerticalExposureCells

/-!
# Boundary walks under inverse rotation

A fixed boundary walk transports to the physical square and its rotated edges
are open throughout the corresponding exposure cell.
-/

open Percolation.Literature

namespace EdgeCrossing

private theorem rotation_symm_apply (n : ℕ) (x : LatticeModels.Site 2) :
    (exposureRotation n).symm x = reflX n (transposeIso x) := by
  rw [RelIso.symm_apply_eq]
  rw [exposureRotation, RelIso.trans_apply, reflX_reflX]
  rw [LatticeModels.Site.eq_iff_two]
  simp only [transposeIso_apply_zero, transposeIso_apply_one, and_self]

/-- The inverse image of a fixed boundary walk lies in the square, joins its
bottom and top sides, and has rotated edges open in every configuration in the cell. -/
theorem inverseRotated_boundaryWalk (n : ℕ) (D : Finset (LatticeModels.Site 2))
    {a b : LatticeModels.Site 2} (π : (LatticeModels.zdGraph 2).Walk a b)
    (ha : a 0 = 0) (hb : b 0 = n)
    (hπ : ∀ z ∈ π.support, z ∈ rectangle n n)
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D n d.edge) :
    let r := exposureRotation n
    let Q := π.map r.symm.toEmbedding.toHom
    (r.symm a) 1 = 0 ∧ (r.symm b) 1 = n ∧
    (∀ z ∈ Q.support, z ∈ rectangle n n) ∧
    (∀ x y, s(x, y) ∈ Q.edges → s(r x, r y) ∈ π.edges) ∧
    ∀ η ∈ verticalExposureCell n D, ∀ x y, s(x, y) ∈ Q.edges →
      s(r x, r y) ∈ BondConfig.relabel (sym2Equiv r.toEquiv)
        (extend (LatticeModels.zdGraph 2) η) := by
  dsimp only
  have hedge : ∀ x y, s(x, y) ∈ (π.map (exposureRotation n).symm.toEmbedding.toHom).edges →
      s(exposureRotation n x, exposureRotation n y) ∈ π.edges := by
    intro x y hxy
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at hxy
    obtain ⟨e, he, heq⟩ := hxy
    have h := congrArg (Sym2.map (exposureRotation n)) heq
    have heq' : e = s(exposureRotation n x, exposureRotation n y) := by
      simpa [Sym2.map_map, Function.comp_def] using h
    simpa [← heq'] using he
  refine ⟨?_, ?_, ?_, hedge, ?_⟩
  · simpa [rotation_symm_apply, reflX_apply_one, transposeIso_apply_one] using ha
  · simpa [rotation_symm_apply, reflX_apply_one, transposeIso_apply_one] using hb
  · intro z hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' := hπ w hw
    change (exposureRotation n).symm w ∈ rectangle n n
    simp only [mem_rectangle_iff] at hw' ⊢
    simp only [rotation_symm_apply, reflX_apply_zero, reflX_apply_one,
      transposeIso_apply_zero, transposeIso_apply_one]
    omega
  · intro η hη x y hxy
    have he := hedge x y hxy
    rw [SimpleGraph.Walk.edges, List.mem_map] at he
    obtain ⟨d, hd, hde⟩ := he
    apply mem_of_isBdryEdge hη
    · apply π.edges_subset_edgeSet
      rw [SimpleGraph.Walk.edges, List.mem_map]
      exact ⟨d, hd, hde⟩
    · rw [← hde]
      exact hbdry d hd

end EdgeCrossing

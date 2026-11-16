import LatticeProb.Probability.Percolation.ExposureBoundaryDualDisjoint
import LatticeProb.Probability.Percolation.FirstContactComponent
import LatticeProb.Probability.Percolation.RotatedDualEndpointWalk
import LatticeProb.Probability.Percolation.RotatedFaceCornerSupport

/-!
# Exposure regions and the first-contact component

A left component separated by a square crossing does not meet the faces of an
achieved dual exposure region.
-/

open Percolation.Literature SimpleGraph

namespace EdgeCrossing

noncomputable section

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2

private theorem mem_subdivide_append {a b c z : V} (p : G.Walk a b) (q : G.Walk b c) :
    z ∈ (subdivideWalk (p.append q)).support ↔
      z ∈ (subdivideWalk p).support ∨ z ∈ (subdivideWalk q).support := by
  simp only [mem_support_subdivideWalk, Walk.mem_support_append_iff, Walk.edges_append,
    List.mem_append]
  aesop

/-- A dual route and a barrier that avoid each other exclude a component vertex from a face. -/
theorem not_mem_firstContactComponent_of_disjoint_dual (n : ℕ) (hn : 1 ≤ n)
    {c d : V} (Q : G.Walk c d)
    (hc : c 1 = 0) (hd : d 1 = n)
    (hQ : ∀ z ∈ Q.support, z ∈ rectangle n n)
    (D : Finset V) (hD : D ⊆ dualRectangle n n)
    (htop : ∀ x ∈ dualTopSide n n, x ∉ D)
    {f v b : V} (hf : f ∈ D) (hb : b ∈ dualBottomSide n n)
    (hx : v 0 = (n : ℤ) - f 1 - 1 ∨ v 0 = (n : ℤ) - f 1)
    (hy : v 1 = f 0 ∨ v 1 = f 0 + 1)
    (q : G.Walk f b) (hq : ∀ x ∈ q.support, x ∈ D)
    (havoid : Disjoint {z | z ∈ (subdivideWalk Q).support}
      {z | z ∈ (subdivideRotatedDualWalk n q).support}) :
    v ∉ firstContactComponent n Q := by
  intro hv
  obtain ⟨t, ht, p, hp⟩ := hv
  have hfix : reflY 0 c = c := by
    rw [LatticeModels.Site.eq_iff_two]
    simp [hc]
  let Qr := ((Q.map (reflY 0).toEmbedding.toHom).reverse).copy rfl hfix
  let H := Qr.append Q
  have hHs : ∀ z, z ∈ H.support ↔ z ∈ Q.support ∨ reflY 0 z ∈ Q.support := by
    intro z
    simp only [H, Walk.mem_support_append_iff, Qr, Walk.support_copy,
      Walk.support_reverse, List.mem_reverse, Walk.support_map, List.mem_map]
    constructor
    · rintro (⟨w, hw, hwz⟩ | hz)
      · right
        have : reflY 0 w = z := hwz
        simpa [← this] using hw
      · exact Or.inl hz
    · rintro (hz | hz)
      · exact Or.inr hz
      · exact Or.inl ⟨reflY 0 z, hz, by simp⟩
  have hH : ∀ z ∈ H.support, -(n : ℤ) ≤ z 0 ∧ z 0 ≤ n ∧
      -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    rcases (hHs z).mp hz with hz | hz
    · have h := mem_rectangle_iff.mp (hQ z hz)
      omega
    · have h := mem_rectangle_iff.mp (hQ (reflY 0 z) hz)
      simp only [reflY_apply_zero, reflY_apply_one] at h
      omega
  have hpH : ∀ x ∈ p.support, x ∉ H.support := by
    intro x hx' hmem
    rcases (hHs x).mp hmem with h | h
    · exact (hp x hx').2.1 h
    · exact (hp x hx').2.2 h
  have hvH : v ∉ H.support := hpH v p.end_mem_support
  have hprimal : Disjoint {z | z ∈ (subdivideWalk p).support}
      {z | z ∈ (subdivideWalk H).support} :=
    disjoint_support_subdivideWalk p H (by
      apply Set.disjoint_left.mpr
      intro x hx' hy'
      exact hpH x hx' hy')
  have hcorner := disjoint_support_rotatedFaceCornerWalk_subdivideWalk n f v hx hy H hvH
  have hdualbounds := subdivideRotatedDualWalk_bounds_of_region n q D hD htop hq
  have hQr : ∀ z ∈ Qr.support, z 1 ≤ 0 := by
    intro z hz
    simp only [Qr, Walk.support_copy, Walk.support_reverse, List.mem_reverse,
      Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have h := mem_rectangle_iff.mp (hQ w hw)
    change reflY 0 w 1 ≤ 0
    simp only [reflY_apply_one]
    omega
  have hdual : Disjoint {z | z ∈ (subdivideRotatedDualWalk n q).support}
      {z | z ∈ (subdivideWalk H).support} := by
    apply Set.disjoint_left.mpr
    intro z hz hmem
    have hsub : z ∈ (subdivideWalk Qr).support ∨ z ∈ (subdivideWalk Q).support := by
      simpa only [H] using (mem_subdivide_append Qr Q).mp hmem
    rcases hsub with hr | hr
    · have hz1 := (hdualbounds z hz).2.2.1
      have hr1 := subdivideWalk_coordinate_bounds Qr 1 (-(n : ℤ)) 0 (by
        intro x hx'
        have hxH : x ∈ H.support := by
          simp only [H, Walk.mem_support_append_iff]
          exact Or.inl hx'
        have h := hH x hxH
        exact ⟨h.2.2.1, hQr x hx'⟩) z hr
      omega
    · exact (Set.disjoint_left.mp havoid) hr hz
  have hendpoint := disjoint_support_rotatedDualEndpointWalk_subdivideWalk n hn hb H
    (fun x hx' => (hH x hx').2.1)
  let P := (((subdivideWalk p).append (rotatedFaceCornerWalk n f v hx hy)).append
    (subdivideRotatedDualWalk n q)).append (rotatedDualEndpointWalk n hb)
  let K := subdivideWalk H
  have hpbound : ∀ z ∈ (subdivideWalk p).support,
      -2 * (n : ℤ) ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 2 ∧
      -2 * (n : ℤ) ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
    intro z hz
    have h0 := subdivideWalk_coordinate_bounds p 0 (-(n : ℤ)) n (by
      intro x hx'
      have h := (mem_centered_square n x).mp (hp x hx').1
      exact ⟨h.1, h.2.1⟩) z hz
    have h1 := subdivideWalk_coordinate_bounds p 1 (-(n : ℤ)) n (by
      intro x hx'
      have h := (mem_centered_square n x).mp (hp x hx').1
      exact ⟨h.2.2.1, h.2.2.2⟩) z hz
    omega
  have hf' : 0 ≤ f 0 ∧ f 0 ≤ (n : ℤ) - 1 ∧ -1 ≤ f 1 ∧ f 1 ≤ (n : ℤ) - 1 := by
    have hr := mem_dualRectangle_iff.mp (hD hf)
    have hne : f 1 ≠ (n : ℤ) := by
      intro heq
      have hft : f ∈ dualTopSide n n := by simp [dualTopSide, hD hf, heq]
      exact htop f hft hf
    omega
  have hPb : ∀ z ∈ P.support, -2 * (n : ℤ) ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 2 ∧
      -2 * (n : ℤ) ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
    intro z hz
    simp only [P, Walk.mem_support_append_iff] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · exact hpbound z hz
    · have h := rotatedFaceCornerWalk_bounds_of_index n f v hx hy hf' z hz
      omega
    · have h := hdualbounds z hz
      omega
    · rcases rotatedDualEndpointWalk_bounds n hn hb z hz with ⟨h0, h1, h2, h3, _⟩
      exact ⟨h0, h1, h2, h3⟩
  have hKb : ∀ z ∈ K.support, -2 * (n : ℤ) ≤ z 0 ∧ z 0 ≤ 2 * (n : ℤ) + 2 ∧
      -2 * (n : ℤ) ≤ z 1 ∧ z 1 ≤ 2 * (n : ℤ) := by
    intro z hz
    have h0 := subdivideWalk_coordinate_bounds H 0 (-(n : ℤ)) n
      (fun x hx' => ⟨(hH x hx').1, (hH x hx').2.1⟩) z hz
    have h1 := subdivideWalk_coordinate_bounds H 1 (-(n : ℤ)) n
      (fun x hx' => ⟨(hH x hx').2.2.1, (hH x hx').2.2.2⟩) z hz
    omega
  have hleft : (t + t) 0 = -2 * (n : ℤ) := by
    simp only [outerLeft, Set.mem_ofPred_eq] at ht
    simp only [Pi.add_apply, ht.1]
    omega
  have hright : rotatedDualEndpoint n b 0 = 2 * (n : ℤ) + 2 := by
    simp [rotatedDualEndpoint]
  have hbottom : (reflY 0 d + reflY 0 d) 1 = -2 * (n : ℤ) := by
    simp only [Pi.add_apply, reflY_apply_one, hd]
    omega
  have htop' : (d + d) 1 = 2 * (n : ℤ) := by
    simp only [Pi.add_apply, hd]
    omega
  obtain ⟨z, hzP, hzK⟩ := exists_mem_support_of_crossing P K hPb hKb hleft hright hbottom htop'
  simp only [P, Walk.mem_support_append_iff] at hzP
  rcases hzP with ((hz | hz) | hz) | hz
  · exact (Set.disjoint_left.mp hprimal) hz hzK
  · exact (Set.disjoint_left.mp hcorner) hz hzK
  · exact (Set.disjoint_left.mp hdual) hz hzK
  · exact (Set.disjoint_left.mp hendpoint) hz hzK

/-- An achieved exposure region has no face incident to the left first-contact component. -/
theorem not_mem_firstContactComponent_of_mem_verticalExposureCell (n : ℕ) (hn : 1 ≤ n)
    (D : Finset V) (hD : D ∈ verticalExposureIndices n)
    {a b : V} (π : G.Walk a b)
    (ha : a 0 = 0) (hb : b 0 = n)
    (hπ : ∀ z ∈ π.support, z ∈ rectangle n n)
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D n d.edge)
    (η : G.edgeSet → Prop) (hη : η ∈ verticalExposureCell n D)
    {f v : V} (hf : f ∈ D)
    (h₀ : exposureRotation n v 0 = f 0 ∨ exposureRotation n v 0 = f 0 + 1)
    (h₁ : exposureRotation n v 1 = f 1 ∨ exposureRotation n v 1 = f 1 + 1) :
    v ∉ firstContactComponent n
      (π.map (exposureRotation n).symm.toEmbedding.toHom) := by
  have hindex := Finset.mem_filter.mp hD
  have hsub : D ⊆ dualRectangle n n := Finset.mem_powerset.mp hindex.1
  have htop := hindex.2.2
  have hQ := inverseRotated_boundaryWalk n D π ha hb hπ hbdry
  have hcorner := rotatedFace_corner_coordinates n f v h₀ h₁
  obtain ⟨j, hj, q, hqs, _, hdis⟩ :=
    exists_dualWalk_disjoint_boundaryWalk_of_mem_verticalExposureCell n D π ha hb hπ hbdry
      η hη hf
  exact not_mem_firstContactComponent_of_disjoint_dual n hn _ hQ.1 hQ.2.1 hQ.2.2.1
    D hsub htop hf hj hcorner.1 hcorner.2 q hqs hdis

/-- A component vertex cannot be incident to a boundary edge of an exposed face. -/
theorem not_mem_firstContactComponent_of_mem_squareEdges (n : ℕ) (hn : 1 ≤ n)
    (D : Finset V) (hD : D ∈ verticalExposureIndices n)
    {a b : V} (π : G.Walk a b)
    (ha : a 0 = 0) (hb : b 0 = n)
    (hπ : ∀ z ∈ π.support, z ∈ rectangle n n)
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D n d.edge)
    (η : G.edgeSet → Prop) (hη : η ∈ verticalExposureCell n D)
    {f v : V} (hf : f ∈ D) {e : Sym2 V}
    (he : e ∈ squareEdges f) (hv : exposureRotation n v ∈ e) :
    v ∉ firstContactComponent n
      (π.map (exposureRotation n).symm.toEmbedding.toHom) := by
  have hcorner :
      (exposureRotation n v 0 = f 0 ∨ exposureRotation n v 0 = f 0 + 1) ∧
      (exposureRotation n v 1 = f 1 ∨ exposureRotation n v 1 = f 1 + 1) := by
    simp only [squareEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp only [Sym2.mem_iff] at hv <;>
      rcases hv with hv | hv <;>
      simp_all [Pi.add_apply]
  exact not_mem_firstContactComponent_of_mem_verticalExposureCell n hn D hD π ha hb hπ hbdry
    η hη hf hcorner.1 hcorner.2

/-- No rotated vertex of the left component is incident to an exposed edge. -/
theorem not_mem_firstContactComponent_of_mem_belowEdges (n : ℕ) (hn : 1 ≤ n)
    (D : Finset V) (hD : D ∈ verticalExposureIndices n)
    {a b : V} (π : G.Walk a b)
    (ha : a 0 = 0) (hb : b 0 = n)
    (hπ : ∀ z ∈ π.support, z ∈ rectangle n n)
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D n d.edge)
    (η : G.edgeSet → Prop) (hη : η ∈ verticalExposureCell n D)
    {v : V} {e : Sym2 V} (he : e ∈ belowEdges D) (hv : exposureRotation n v ∈ e) :
    v ∉ firstContactComponent n
      (π.map (exposureRotation n).symm.toEmbedding.toHom) := by
  obtain ⟨f, hf, he⟩ := Finset.mem_biUnion.mp he
  exact not_mem_firstContactComponent_of_mem_squareEdges n hn D hD π ha hb hπ hbdry
    η hη hf he hv

/-- The exclusion for a supplied physical bottom-to-top boundary walk. -/
theorem not_mem_firstContactComponent_of_rotated_boundary (n : ℕ) (hn : 1 ≤ n)
    (D : Finset V) (hD : D ∈ verticalExposureIndices n)
    {c d : V} (Q : G.Walk c d)
    (hc : c 1 = 0) (hd : d 1 = n)
    (hQ : ∀ z ∈ Q.support, z ∈ rectangle n n)
    (hbdry : ∀ e ∈ Q.darts,
      IsBdryEdge D n s(exposureRotation n e.fst, exposureRotation n e.snd))
    (η : G.edgeSet → Prop) (hη : η ∈ verticalExposureCell n D)
    {v : V} {e : Sym2 V} (he : e ∈ belowEdges D) (hv : exposureRotation n v ∈ e) :
    v ∉ firstContactComponent n Q := by
  let r := exposureRotation n
  let π := Q.map r.toEmbedding.toHom
  have ha : (r c) 0 = 0 := by
    simpa [r, exposureRotation, RelIso.trans_apply, transposeIso_apply_zero, reflX_apply_one]
      using hc
  have hb : (r d) 0 = n := by
    simpa [r, exposureRotation, RelIso.trans_apply, transposeIso_apply_zero, reflX_apply_one]
      using hd
  have hπ : ∀ z ∈ π.support, z ∈ rectangle n n := by
    intro z hz
    simp only [π, Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have h := mem_rectangle_iff.mp (hQ w hw)
    apply mem_rectangle_iff.mpr
    change 0 ≤ (r w) 0 ∧ (r w) 0 ≤ n ∧ 0 ≤ (r w) 1 ∧ (r w) 1 ≤ n
    simp only [r, exposureRotation, RelIso.trans_apply, transposeIso_apply_zero,
      transposeIso_apply_one, reflX_apply_zero, reflX_apply_one]
    omega
  have hπbdry : ∀ e ∈ π.darts, IsBdryEdge D n e.edge := by
    intro e he'
    simp only [π, Walk.darts_map, List.mem_map] at he'
    obtain ⟨e', he', rfl⟩ := he'
    exact hbdry e' he'
  have hs : (π.map r.symm.toEmbedding.toHom).support = Q.support := by
    dsimp only [π]
    rw [Walk.support_map, Walk.support_map, List.map_map]
    change Q.support.map (fun x => r.symm (r x)) = Q.support
    simp
  have hresult := not_mem_firstContactComponent_of_mem_belowEdges n hn D hD π ha hb hπ
    hπbdry η hη he hv
  change v ∉ firstContactComponent n (π.map r.symm.toEmbedding.toHom) at hresult
  simpa only [firstContactComponent, hs] using hresult

/-- A vertex of the left component cannot be a corner of an achieved exposed face. -/
theorem not_mem_firstContactComponent_of_rotated_face (n : ℕ) (hn : 1 ≤ n)
    (D : Finset V) (hD : D ∈ verticalExposureIndices n)
    {c d : V} (Q : G.Walk c d)
    (hc : c 1 = 0) (hd : d 1 = n)
    (hQ : ∀ z ∈ Q.support, z ∈ rectangle n n)
    (hbdry : ∀ e ∈ Q.darts,
      IsBdryEdge D n s(exposureRotation n e.fst, exposureRotation n e.snd))
    (η : G.edgeSet → Prop) (hη : η ∈ verticalExposureCell n D)
    {f v : V} (hf : f ∈ D)
    (h₀ : exposureRotation n v 0 = f 0 ∨ exposureRotation n v 0 = f 0 + 1)
    (h₁ : exposureRotation n v 1 = f 1 ∨ exposureRotation n v 1 = f 1 + 1) :
    v ∉ firstContactComponent n Q := by
  have hcorner : exposureRotation n v = f ∨
      exposureRotation n v = f + Pi.single 0 1 ∨
      exposureRotation n v = f + Pi.single 1 1 ∨
      exposureRotation n v = f + Pi.single 1 1 + Pi.single 0 1 := by
    rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
    · left; rw [LatticeModels.Site.eq_iff_two]; exact ⟨h₀, h₁⟩
    · right; right; left
      rw [LatticeModels.Site.eq_iff_two]
      simpa [Pi.add_apply] using And.intro h₀ h₁
    · right; left
      rw [LatticeModels.Site.eq_iff_two]
      simpa [Pi.add_apply] using And.intro h₀ h₁
    · right; right; right
      rw [LatticeModels.Site.eq_iff_two]
      simpa [Pi.add_apply] using And.intro h₀ h₁
  have hex : ∃ e ∈ belowEdges D, exposureRotation n v ∈ e := by
    rcases hcorner with h | h | h | h
    · refine ⟨s(f, f + Pi.single 0 1), ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨f, hf, by simp [squareEdges]⟩
      · rw [h]; exact Sym2.mem_mk_left _ _
    · refine ⟨s(f, f + Pi.single 0 1), ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨f, hf, by simp [squareEdges]⟩
      · rw [h]; exact Sym2.mem_mk_right _ _
    · refine ⟨s(f + Pi.single 1 1, f + Pi.single 1 1 + Pi.single 0 1), ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨f, hf, by simp [squareEdges]⟩
      · rw [h]; exact Sym2.mem_mk_left _ _
    · refine ⟨s(f + Pi.single 1 1, f + Pi.single 1 1 + Pi.single 0 1), ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨f, hf, by simp [squareEdges]⟩
      · rw [h]; exact Sym2.mem_mk_right _ _
  obtain ⟨e, he, hv⟩ := hex
  exact not_mem_firstContactComponent_of_rotated_boundary n hn D hD Q hc hd hQ hbdry η hη he hv

end
end EdgeCrossing

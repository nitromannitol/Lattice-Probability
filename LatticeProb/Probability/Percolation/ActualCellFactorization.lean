import LatticeProb.Probability.Percolation.ExposureComponentSeparation
import LatticeProb.Probability.Percolation.ExposureIndependence

/-!
# Independence of exposure cells and first contact

A fixed boundary walk separates the first-contact support from the edges
that determine its dual exposure cell.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature SimpleGraph
open scoped ProbabilityTheory

noncomputable section
namespace EdgeCrossing

private abbrev V := LatticeModels.Site 2
private abbrev G := LatticeModels.zdGraph 2
private abbrev Edge := G.edgeSet
private abbrev Config := Edge → Prop

private def exposureEdges (n : ℕ) (D : Finset V) : Finset Edge := by
  classical
  exact ((belowEdges D).image (sym2Equiv (exposureRotation n).toEquiv).symm).subtype
    (fun e => e ∈ G.edgeSet)

private theorem mem_exposureEdges_iff (n : ℕ) (D : Finset V) (e : Edge) :
    e ∈ exposureEdges n D ↔ sym2Equiv (exposureRotation n).toEquiv e.1 ∈ belowEdges D := by
  classical
  let r := sym2Equiv (exposureRotation n).toEquiv
  simp only [exposureEdges, Finset.mem_subtype, Finset.mem_image]
  change (∃ a ∈ belowEdges D, r.symm a = e.1) ↔ r e.1 ∈ belowEdges D
  constructor
  · rintro ⟨a, ha, h⟩
    rw [← h, r.apply_symm_apply]
    exact ha
  · intro h
    exact ⟨r e.1, h, r.symm_apply_apply _⟩

private theorem exposureCell_congr (n : ℕ) (D : Finset V) (η ξ : Config)
    (h : ∀ e ∈ exposureEdges n D, η e = ξ e) :
    η ∈ verticalExposureCell n D ↔ ξ ∈ verticalExposureCell n D := by
  classical
  apply mem_verticalExposureCell_iff_of_agree
  intro e he
  let r := sym2Equiv (exposureRotation n).toEquiv
  rw [BondConfig.mem_relabel_iff, BondConfig.mem_relabel_iff]
  change (∃ h : r.symm e ∈ G.edgeSet, η ⟨r.symm e, h⟩) ↔
    (∃ h : r.symm e ∈ G.edgeSet, ξ ⟨r.symm e, h⟩)
  by_cases hg : r.symm e ∈ G.edgeSet
  · have hs : (⟨r.symm e, hg⟩ : Edge) ∈ exposureEdges n D := by
      rw [mem_exposureEdges_iff]
      change r (r.symm e) ∈ belowEdges D
      rwa [r.apply_symm_apply]
    have hh := h ⟨r.symm e, hg⟩ hs
    constructor
    · rintro ⟨_, hη⟩
      exact ⟨hg, hh.mp hη⟩
    · rintro ⟨_, hξ⟩
      exact ⟨hg, hh.mpr hξ⟩
  · simp [hg]

/-- A fixed boundary walk makes its exposure cell independent of first contact. -/
theorem verticalExposureCell_real_inter_firstContact (n : ℕ) (hn : 1 ≤ n)
    (D : Finset V) (hD : D ∈ verticalExposureIndices n)
    {c d : V} (Q : G.Walk c d)
    (hc : c 1 = 0) (hd : d 1 = n)
    (hQ : ∀ z ∈ Q.support, z ∈ rectangle n n)
    (hbdry : ∀ e ∈ Q.darts,
      IsBdryEdge D n s(exposureRotation n e.fst, exposureRotation n e.snd)) :
    (Measure.infinitePi (fun _ : Edge => bernoulliMeasure True False half)).real
        (verticalExposureCell n D ∩ firstContact n Q (Bool.not true)) =
      (Measure.infinitePi (fun _ : Edge => bernoulliMeasure True False half)).real
        (verticalExposureCell n D) *
      (Measure.infinitePi (fun _ : Edge => bernoulliMeasure True False half)).real
        (firstContact n Q (Bool.not true)) := by
  classical
  by_cases hex : (verticalExposureCell n D).Nonempty
  · obtain ⟨η, hη⟩ := hex
    have hdis : Disjoint (exposureEdges n D) (firstContactComponentEdges n Q) := by
      apply Finset.disjoint_left.mpr
      intro e he hT
      obtain ⟨_, v, hv, hvcomp⟩ := (mem_firstContactComponentEdges_iff n Q e).mp hT
      have he' := (mem_exposureEdges_iff n D e).mp he
      have hv' : exposureRotation n v ∈ sym2Equiv (exposureRotation n).toEquiv e.1 := by
        exact Sym2.mem_map.mpr ⟨v, hv, rfl⟩
      exact (not_mem_firstContactComponent_of_rotated_boundary n hn D hD Q hc hd hQ hbdry
        η hη he' hv') hvcomp
    exact edge_product_real_inter_of_disjoint half _ _ hdis _ _
      (exposureCell_congr n D) (firstContact_component_congr n Q (Bool.not true))
  · have hempty : verticalExposureCell n D = ∅ := Set.not_nonempty_iff_eq_empty.mp hex
    simp [hempty]

end EdgeCrossing

import LatticeProb.Probability.Percolation.VerticalJoinedExposure

/-!
# Dual-region cells for vertical crossings

The dual region explored from the right side of a square gives a finite family
of measurable, disjoint cells for its vertical crossing event.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

private abbrev Config := (LatticeModels.zdGraph 2).edgeSet → Prop
private abbrev criticalMeasure : Measure Config :=
  Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
    bernoulliMeasure True False half)

/-- Rotation carrying the right side of the square to its bottom side. -/
def exposureRotation (n : ℕ) : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2 :=
  (reflX n).trans transposeIso

/-- The dual region reached from the right side after rotating the configuration. -/
def rightDualRegion (n : ℕ) (η : Config) : Finset (LatticeModels.Site 2) :=
  dualBelow n (BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
    (extend (LatticeModels.zdGraph 2) η))

/-- The possible dual regions separating the left and right sides of the square. -/
def verticalExposureIndices (n : ℕ) : Finset (Finset (LatticeModels.Site 2)) :=
  (dualRectangle n n).powerset.filter fun D =>
    (∀ f ∈ dualBottomSide n n, f ∈ D) ∧ ∀ f ∈ dualTopSide n n, f ∉ D

/-- Configurations with a specified explored dual region. -/
def verticalExposureCell (n : ℕ) (D : Finset (LatticeModels.Site 2)) : Set Config :=
  {η | rightDualRegion n η = D}

/-- Exposure cells are measurable. -/
theorem measurableSet_verticalExposureCell (n : ℕ) (D : Finset (LatticeModels.Site 2)) :
    MeasurableSet (verticalExposureCell n D) := by
  exact ((determinedBy_dualBelow_eq n D).measurableSet_of_finset).preimage
    ((BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)).measurable.comp
      (measurable_extend _))

/-- Distinct dual-region cells are disjoint. -/
theorem pairwiseDisjoint_verticalExposureCell (n : ℕ) :
    (↑(verticalExposureIndices n) : Set (Finset (LatticeModels.Site 2))).PairwiseDisjoint
      (verticalExposureCell n) := by
  intro D₁ _ D₂ _ hne
  rw [Function.onFun, Set.disjoint_left]
  intro η h₁ h₂
  exact hne (h₁.symm.trans h₂)

private theorem exposureRotation_symm_apply (n : ℕ) (x : LatticeModels.Site 2) :
    (exposureRotation n).symm x = reflX n (transposeIso x) := by
  rw [RelIso.symm_apply_eq]
  rw [exposureRotation, RelIso.trans_apply, reflX_reflX]
  rw [LatticeModels.Site.eq_iff_two]
  simp only [transposeIso_apply_zero, transposeIso_apply_one, and_self]

private theorem exposureRotation_toEquiv_symm_apply (n : ℕ) (x : LatticeModels.Site 2) :
    (exposureRotation n).toEquiv.symm x = reflX n (transposeIso x) := by
  exact exposureRotation_symm_apply n x

private theorem image_exposureRotation_square (n : ℕ) :
    (exposureRotation n).toEquiv '' (rectangle n n : Set (LatticeModels.Site 2)) =
      (rectangle n n : Set (LatticeModels.Site 2)) := by
  ext x
  rw [Equiv.image_eq_preimage_symm]
  simp only [Set.mem_preimage, Finset.mem_coe, mem_rectangle_iff]
  simp only [exposureRotation_toEquiv_symm_apply, reflX_apply_zero, reflX_apply_one,
    transposeIso_apply_zero, transposeIso_apply_one]
  omega

private theorem image_exposureRotation_bottom (n : ℕ) :
    (exposureRotation n).toEquiv '' (bottomSide n n : Set (LatticeModels.Site 2)) =
      (leftSide n n : Set (LatticeModels.Site 2)) := by
  ext x
  rw [Equiv.image_eq_preimage_symm]
  simp only [Set.mem_preimage, Finset.mem_coe, bottomSide, leftSide, Finset.mem_filter,
    mem_rectangle_iff]
  simp only [exposureRotation_toEquiv_symm_apply, reflX_apply_zero, reflX_apply_one,
    transposeIso_apply_zero, transposeIso_apply_one]
  omega

private theorem image_exposureRotation_top (n : ℕ) :
    (exposureRotation n).toEquiv '' (topSide n n : Set (LatticeModels.Site 2)) =
      (rightSide n n : Set (LatticeModels.Site 2)) := by
  ext x
  rw [Equiv.image_eq_preimage_symm]
  simp only [Set.mem_preimage, Finset.mem_coe, topSide, rightSide, Finset.mem_filter,
    mem_rectangle_iff]
  simp only [exposureRotation_toEquiv_symm_apply, reflX_apply_zero, reflX_apply_one,
    transposeIso_apply_zero, transposeIso_apply_one]
  omega

private theorem mem_rotated_lrCrossing_iff (n : ℕ) (η : Config) :
    BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
      (extend (LatticeModels.zdGraph 2) η) ∈ lrCrossing n n ↔
    η ∈ crossingIn (rectangle n n) (bottomSide n n) (topSide n n) := by
  have h := preimage_relabel_openCrossing (exposureRotation n).toEquiv
    (rectangle n n : Set (LatticeModels.Site 2)) (bottomSide n n) (topSide n n)
  rw [image_exposureRotation_square, image_exposureRotation_bottom,
    image_exposureRotation_top] at h
  exact (Set.ext_iff.mp h (extend (LatticeModels.zdGraph 2) η))

/-- Every vertical crossing belongs to a cell indexed by its explored dual region. -/
theorem vertical_crossing_subset_iUnion_exposureCell (n : ℕ) :
    crossingIn (rectangle n n) (bottomSide n n) (topSide n n) ⊆
      ⋃ D ∈ verticalExposureIndices n, verticalExposureCell n D := by
  intro η hη
  let ω := BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
    (extend (LatticeModels.zdGraph 2) η)
  have hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet := by
    intro e he
    change e ∈ BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
      (extend (LatticeModels.zdGraph 2) η) at he
    rw [BondConfig.relabel_apply] at he
    obtain ⟨e', he', rfl⟩ := he
    exact (sym2Equiv_mem_edgeSet_iff (exposureRotation n) e').2 (extend_subset _ _ he')
  refine Set.mem_iUnion₂.mpr ⟨rightDualRegion n η, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr dualBelow_subset, ?_, ?_⟩
  · intro f hf
    exact mem_dualBelow_of_mem_dualBottomSide hf
  · intro f hf
    exact not_mem_dualBelow_of_lrCrossing hω ((mem_rotated_lrCrossing_iff n η).2 hη) hf

/-- Every indexed cell consists of vertical crossings. -/
theorem iUnion_exposureCell_subset_vertical_crossing (n : ℕ) :
    (⋃ D ∈ verticalExposureIndices n, verticalExposureCell n D) ⊆
      crossingIn (rectangle n n) (bottomSide n n) (topSide n n) := by
  intro η hη
  obtain ⟨D, hD, hcell⟩ := Set.mem_iUnion₂.mp hη
  obtain ⟨_, hbot, htop⟩ := Finset.mem_filter.mp hD
  obtain ⟨a, b, ha, hb, π, hπ, hbdry⟩ := exists_bdryWalk hbot htop
  apply (mem_rotated_lrCrossing_iff n η).mp
  refine ⟨a, ?_, b, ?_, mem_openConnIn_of_walk π hπ ?_⟩
  · simp only [Finset.mem_coe, leftSide, Finset.mem_filter]
    exact ⟨hπ a (by simp), ha⟩
  · simp only [Finset.mem_coe, rightSide, Finset.mem_filter]
    exact ⟨hπ b (by simp), hb⟩
  · intro e he
    rw [SimpleGraph.Walk.edges, List.mem_map] at he
    obtain ⟨d, hd, rfl⟩ := he
    apply mem_of_isBdryEdge hcell
    · apply π.edges_subset_edgeSet
      rw [SimpleGraph.Walk.edges, List.mem_map]
      exact ⟨d, hd, rfl⟩
    · exact hbdry d hd

/-- The vertical crossing is exactly the union of its dual-region cells. -/
theorem iUnion_exposureCell_eq_vertical_crossing (n : ℕ) :
    (⋃ D ∈ verticalExposureIndices n, verticalExposureCell n D) =
      crossingIn (rectangle n n) (bottomSide n n) (topSide n n) :=
  Set.Subset.antisymm (iUnion_exposureCell_subset_vertical_crossing n)
    (vertical_crossing_subset_iUnion_exposureCell n)

/-- Agreement on the exposed rotated edges preserves membership in an exposure cell. -/
theorem mem_verticalExposureCell_iff_of_agree (n : ℕ) (D : Finset (LatticeModels.Site 2))
    (η ξ : Config)
    (h : ∀ e ∈ belowEdges D,
      e ∈ BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
          (extend (LatticeModels.zdGraph 2) η) ↔
      e ∈ BondConfig.relabel (sym2Equiv (exposureRotation n).toEquiv)
          (extend (LatticeModels.zdGraph 2) ξ)) :
    η ∈ verticalExposureCell n D ↔ ξ ∈ verticalExposureCell n D := by
  apply (determinedBy_iff _ _).mp (determinedBy_dualBelow_eq n D)
  ext e
  simp only [Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · rintro ⟨heη, he⟩
    exact ⟨(h e he).mp heη, he⟩
  · rintro ⟨heξ, he⟩
    exact ⟨(h e he).mpr heξ, he⟩

/-- The dual-region cells specialize the finite-exposure reduction. -/
theorem vertical_crossing_div_four_le_joined_of_dual_cells (n : ℕ)
    (E : Finset (LatticeModels.Site 2) → Set Config)
    (hE : ∀ D ∈ verticalExposureIndices n, MeasurableSet (E D))
    (hindep : ∀ D ∈ verticalExposureIndices n,
      criticalMeasure.real (verticalExposureCell n D ∩ E D) =
        criticalMeasure.real (verticalExposureCell n D) * criticalMeasure.real (E D))
    (hprob : ∀ D ∈ verticalExposureIndices n, (1 / 4 : ℝ) ≤ criticalMeasure.real (E D))
    (hjoin : ∀ D ∈ verticalExposureIndices n, verticalExposureCell n D ∩ E D ⊆
      joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n)) :
    criticalMeasure.real (crossingIn (rectangle n n) (bottomSide n n) (topSide n n)) / 4 ≤
      criticalMeasure.real (joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n)) := by
  exact vertical_crossing_div_four_le_joined_of_exposure n (verticalExposureIndices n)
    (verticalExposureCell n) E (vertical_crossing_subset_iUnion_exposureCell n)
    (pairwiseDisjoint_verticalExposureCell n) (fun D _ => measurableSet_verticalExposureCell n D)
    hE hindep hprob hjoin

end EdgeCrossing

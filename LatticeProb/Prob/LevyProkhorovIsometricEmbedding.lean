import LatticeProb.Prob.LevyProkhorovMaps

/-!
# Lévy–Prokhorov distance under isometric embeddings

A measurable isometric embedding preserves the distance of arbitrary measures.
-/

open MeasureTheory Metric Set

namespace LatticeProb

/-- A measurable isometric embedding preserves Lévy–Prokhorov edistance. -/
theorem levyProkhorovEDist_map_eq_of_isometry
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]
    {f : X → Y} (hf : Isometry f) (hm : MeasurableEmbedding f)
    (μ ν : Measure X) :
    levyProkhorovEDist (μ.map f) (ν.map f) = levyProkhorovEDist μ ν := by
  apply le_antisymm
  · exact levyProkhorovEDist_map_le_of_lipschitz_one hf.lipschitzWith hm.measurable μ ν
  · apply levyProkhorovEDist_le_of_forall
    intro ε A hε _ hA
    have himage : MeasurableSet (f '' A) := hm.measurableSet_image.mpr hA
    have hpre : f ⁻¹' (f '' A) = A := hm.injective.preimage_image A
    have hthick : f ⁻¹' thickening ε.toReal (f '' A) = thickening ε.toReal A := by
      ext x
      simp only [mem_preimage, mem_thickening_iff_exists_edist_lt]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, hxy⟩
        exact ⟨y, hy, by simpa only [hf.edist_eq] using hxy⟩
      · rintro ⟨y, hy, hxy⟩
        exact ⟨f y, ⟨y, hy, rfl⟩, by simpa only [hf.edist_eq] using hxy⟩
    have hl := left_measure_le_of_levyProkhorovEDist_lt hε himage
    have hr := right_measure_le_of_levyProkhorovEDist_lt hε himage
    rw [Measure.map_apply hm.measurable himage,
      Measure.map_apply hm.measurable isOpen_thickening.measurableSet, hpre, hthick] at hl hr
    exact ⟨hl, hr⟩

/-- Measures supported on a measurable subspace have the same Lévy–Prokhorov
edistance in the subspace and in the ambient space. -/
theorem levyProkhorovEDist_comap_subtype_eq
    {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) (μ ν : Measure X)
    (hμ : ∀ᵐ x ∂μ, x ∈ S) (hν : ∀ᵐ x ∂ν, x ∈ S) :
    levyProkhorovEDist (μ.comap ((↑) : S → X)) (ν.comap ((↑) : S → X)) =
      levyProkhorovEDist μ ν := by
  have h := levyProkhorovEDist_map_eq_of_isometry
    (isometry_subtype_coe : Isometry ((↑) : S → X)) (MeasurableEmbedding.subtype_coe hS)
    (μ.comap ((↑) : S → X)) (ν.comap ((↑) : S → X))
  rw [map_comap_subtype_coe hS, map_comap_subtype_coe hS,
    Measure.restrict_eq_self_of_ae_mem hμ, Measure.restrict_eq_self_of_ae_mem hν] at h
  exact h.symm

end LatticeProb

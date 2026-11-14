import LatticeProb.Analysis.AreaParametrizedCurveCells

/-! # Time interval containment for area-parametrized curves -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A nondegenerate interval whose image is contained in the image of another
nondegenerate interval is itself contained in that interval. -/
theorem Icc_subset_of_area_curve_image_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (η : ℝ → X) (μ : Measure X)
    (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {p q s t : ℝ} (hpq : p < q) (hst : s < t)
    (hsub : η '' Icc p q ⊆ η '' Icc s t) : Icc p q ⊆ Icc s t := by
  have hleft : s ≤ p := by
    by_contra hn
    have hps : p < s := lt_of_not_ge hn
    have hpc : p < min q s := lt_min hpq hps
    have hzero := measure_image_Icc_inter_image_Icc_eq_zero hη hμ hpc
      (min_le_right q s) hst
    have hsubset : η '' Icc p (min q s) ⊆
        η '' Icc p (min q s) ∩ η '' Icc s t := by
      intro x hx
      exact ⟨hx, hsub (image_mono (Icc_subset_Icc le_rfl (min_le_left q s)) hx)⟩
    have hle := measure_mono (μ := μ) hsubset
    rw [hzero, hμ _ _ hpc] at hle
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hpc))) hle
  have hright : q ≤ t := by
    by_contra hn
    have htq : t < q := lt_of_not_ge hn
    have hcq : max p t < q := max_lt hpq htq
    have hzero := measure_image_Icc_inter_image_Icc_eq_zero hη hμ hst
      (le_max_right p t) hcq
    have hsubset : η '' Icc (max p t) q ⊆
        η '' Icc s t ∩ η '' Icc (max p t) q := by
      intro x hx
      exact ⟨hsub (image_mono (Icc_subset_Icc (le_max_left p t) le_rfl) hx), hx⟩
    have hle := measure_mono (μ := μ) hsubset
    rw [hzero, hμ _ _ hcq] at hle
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hcq))) hle
  exact Icc_subset_Icc hleft hright

/-- Nondegenerate intervals with the same image under an area-parametrized
curve have the same endpoints. -/
theorem endpoints_eq_of_area_curve_image_eq
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (η : ℝ → X) (μ : Measure X)
    (hη : Continuous η)
    (hμ : ∀ a b, a < b → μ (η '' Icc a b) = ENNReal.ofReal (b - a))
    {p q s t : ℝ} (hpq : p < q) (hst : s < t)
    (heq : η '' Icc p q = η '' Icc s t) : p = s ∧ q = t := by
  have h₁ := Icc_subset_of_area_curve_image_subset η μ hη hμ hpq hst heq.subset
  have h₂ := Icc_subset_of_area_curve_image_subset η μ hη hμ hst hpq heq.symm.subset
  exact ⟨le_antisymm (h₂ ⟨le_rfl, hst.le⟩).1 (h₁ ⟨le_rfl, hpq.le⟩).1,
    le_antisymm (h₁ ⟨hpq.le, le_rfl⟩).2 (h₂ ⟨hst.le, le_rfl⟩).2⟩

end LatticeProb

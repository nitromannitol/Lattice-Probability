import LatticeProb.Prob.Strassen.Defs

/-!
# C. Finite-dimensional marginal weights

The weight `wt μ F y` of a finite pattern `y : F → Bool` under `μ`, for `F : Finset S`: it is
nonnegative and sums to `1` over all patterns on `F`, the sum of pattern weights over a finset `U`
of patterns equals the real mass of the corresponding cylinder event, and up-set domination for
`μ, ν` transfers to a domination of pattern weights over every upper set of patterns
(`sum_wt_le_sum_wt_of_isUpperSet`), since the preimage under `F.restrict` of an upper set of
patterns is an increasing set.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

namespace StrassenAux

attribute [local instance 10] Classical.propDecidable

/-- Weight of the finite pattern `y` on `F` under `μ`. -/
noncomputable def wt {S : Type} (μ : Measure (S → Bool)) (F : Finset S) (y : F → Bool) : ℝ :=
  (μ (F.restrict ⁻¹' {y})).toReal

/-- The preimage of a set under the restriction map `F.restrict` is measurable. -/
theorem measurableSet_preimage_restrict {S : Type} (F : Finset S) (T : Set (F → Bool)) :
    MeasurableSet (F.restrict ⁻¹' T : Set (S → Bool)) := by
  haveI : DiscreteMeasurableSpace (F → Bool) := inferInstance
  exact (MeasurableSet.of_discrete (α := F → Bool)).preimage (Finset.measurable_restrict F)


/-- The sum of pattern weights `wt μ F` over a finset `U` equals the real mass of the corresponding
cylinder event. -/
theorem sum_wt_eq_measure_preimage_restrict_toReal {S : Type} (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ]
    (F : Finset S) (U : Finset (F → Bool)) :
    ∑ y ∈ U, wt μ F y = (μ (F.restrict ⁻¹' (U : Set (F → Bool)))).toReal := by
  have hg : Measurable (F.restrict : (S → Bool) → (↥F → Bool)) := Finset.measurable_restrict F
  have hmeas : ∀ y ∈ U,
      MeasurableSet ((F.restrict : (S → Bool) → (↥F → Bool)) ⁻¹' ({y} : Set (↥F → Bool))) :=
    fun y _ => (measurableSet_singleton y).preimage hg
  have hsum := sum_measureReal_preimage_singleton (μ := μ) U
    (f := (F.restrict : (S → Bool) → (↥F → Bool))) hmeas
  simp only [measureReal_def] at hsum
  simp only [wt]
  exact hsum


/-- The pattern weights `wt μ F` are nonnegative and sum to `1`. -/
theorem wt_nonneg_and_sum_wt_eq_one {S : Type} (μ : Measure (S → Bool))
    [IsProbabilityMeasure μ]
    (F : Finset S) : (∀ y, 0 ≤ wt μ F y) ∧ ∑ y, wt μ F y = 1 := by
  refine ⟨fun y => ENNReal.toReal_nonneg, ?_⟩
  rw [sum_wt_eq_measure_preimage_restrict_toReal μ F (Finset.univ : Finset (F → Bool))]
  simp


/-- The preimage under `F.restrict` of an upper set of patterns is an increasing set. -/
private theorem isIncreasingSet_preimage_restrict_of_isUpperSet {S : Type} (F : Finset S)
    (U : Set (F → Bool)) (hU : IsUpperSet U) :
    IsIncreasingSet (F.restrict ⁻¹' U : Set (S → Bool)) := by
  intro ω ω' hω h
  refine hU ?_ hω
  rw [Pi.le_def]
  intro i
  exact Bool.le_iff_imp.mpr (h (i : S))


/-- Domination transfers to upper sets of finite patterns: `∑_U wt ν F ≤ ∑_U wt μ F`. -/
theorem sum_wt_le_sum_wt_of_isUpperSet {S : Type} (μ ν : Measure (S → Bool))
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hdom : ∀ A : Set (S → Bool), MeasurableSet A → IsIncreasingSet A → ν A ≤ μ A)
    (F : Finset S) (U : Finset (F → Bool)) (hU : IsUpperSet (U : Set (F → Bool))) :
    ∑ y ∈ U, wt ν F y ≤ ∑ x ∈ U, wt μ F x := by
  rw [sum_wt_eq_measure_preimage_restrict_toReal ν F U,
    sum_wt_eq_measure_preimage_restrict_toReal μ F U]
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (hdom _ (measurableSet_preimage_restrict F (U : Set (F → Bool)))
      (isIncreasingSet_preimage_restrict_of_isUpperSet F (U : Set (F → Bool)) hU))

end StrassenAux

end LatticeProb

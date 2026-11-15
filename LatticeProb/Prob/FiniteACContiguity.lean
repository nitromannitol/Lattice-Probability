import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Uniform small-set bounds from finite absolute continuity -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace LatticeProb

/-- A finite measure absolutely continuous with respect to a finite measure is
uniformly small on sets of small reference measure. -/
theorem exists_measure_le_of_absolutelyContinuous
    {E : Type*} [MeasurableSpace E] (μ ν : Measure E)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ d : ℝ≥0∞, 0 < d ∧ ∀ T : Set E, ν T ≤ d → μ T ≤ e := by
  have hRN := Measure.withDensity_rnDeriv_eq μ ν hac
  have hfin : (∫⁻ x, μ.rnDeriv ν x ∂ν) ≠ ∞ := by
    have h := congrArg (fun m : Measure E => m Set.univ) hRN
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    rw [h]
    exact measure_ne_top μ Set.univ
  obtain ⟨d, hd, hbound⟩ := exists_pos_setLIntegral_lt_of_measure_lt hfin he.ne'
  obtain ⟨d', hd', hdd'⟩ := exists_between hd
  refine ⟨d', hd', fun T hT => ?_⟩
  calc
    μ T = ν.withDensity (μ.rnDeriv ν) T := by rw [hRN]
    _ = ∫⁻ x in T, μ.rnDeriv ν x ∂ν := withDensity_apply' _ _
    _ ≤ e := (hbound T (lt_of_le_of_lt hT hdd')).le

/-- Image laws dominated by one finite absolutely continuous measure have a
common small-set bound, without any independence assumptions. -/
theorem preimage_measure_le_of_dominated_absolutelyContinuous
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X : ι → Ω → E) (hX : ∀ i, AEMeasurable (X i) P)
    (hdom : ∀ i, Measure.map (X i) P ≤ μ) (hac : μ ≪ ν)
    {e : ℝ≥0∞} (he : 0 < e) :
    ∃ d : ℝ≥0∞, 0 < d ∧ ∀ i T, ν T ≤ d → P ((X i) ⁻¹' T) ≤ e := by
  obtain ⟨d, hd, hbound⟩ := exists_measure_le_of_absolutelyContinuous μ ν hac he
  refine ⟨d, hd, fun i T hT => ?_⟩
  obtain ⟨S, hTS, hS, hν⟩ := exists_measurable_superset ν T
  calc
    P ((X i) ⁻¹' T) ≤ P ((X i) ⁻¹' S) := measure_mono (preimage_mono hTS)
    _ = Measure.map (X i) P S := (Measure.map_apply₀ (hX i) hS.nullMeasurableSet).symm
    _ ≤ μ S := hdom i S
    _ ≤ e := hbound S (hν ▸ hT)

end LatticeProb

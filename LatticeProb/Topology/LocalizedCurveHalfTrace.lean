import Mathlib

/-! # Half-traces of localized curve segments -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- Each length-`ε` interval containing `t₀` lies in the two-sided window and
contains at least one of the two half-intervals adjoining `t₀`. -/
theorem localized_interval_contains_half {ε t₀ s : ℝ}
    (hs : s ∈ Icc t₀ (t₀ + ε)) :
    Icc (s - ε) s ⊆ Icc (t₀ - ε) (t₀ + ε) ∧
      (Icc (t₀ - ε / 2) t₀ ⊆ Icc (s - ε) s ∨
       Icc t₀ (t₀ + ε / 2) ⊆ Icc (s - ε) s) := by
  refine ⟨Icc_subset_Icc (by linarith [hs.1]) hs.2, ?_⟩
  by_cases h : s ≤ t₀ + ε / 2
  · left
    exact Icc_subset_Icc (by linarith) hs.1
  · right
    exact Icc_subset_Icc (by linarith [hs.2]) (by linarith)

/-- If both half-traces leave a set, every localized segment leaves it. -/
theorem localized_curve_segment_not_subset {X : Type*} (η : ℝ → X) (U : Set X)
    {ε t₀ s : ℝ} (hs : s ∈ Icc t₀ (t₀ + ε))
    (hleft : ¬ η '' Icc (t₀ - ε / 2) t₀ ⊆ U)
    (hright : ¬ η '' Icc t₀ (t₀ + ε / 2) ⊆ U) :
    ¬ η '' Icc (s - ε) s ⊆ U := by
  intro hsub
  rcases (localized_interval_contains_half hs).2 with h | h
  · exact hleft ((image_mono h).trans hsub)
  · exact hright ((image_mono h).trans hsub)

/-- The measure of a localized segment is bounded below by the smaller
measure of the two half-traces. -/
theorem min_half_trace_measure_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (η : ℝ → X) {ε t₀ s : ℝ}
    (hs : s ∈ Icc t₀ (t₀ + ε)) :
    min (μ (η '' Icc (t₀ - ε / 2) t₀)) (μ (η '' Icc t₀ (t₀ + ε / 2))) ≤
      μ (η '' Icc (s - ε) s) := by
  rcases (localized_interval_contains_half hs).2 with h | h
  · exact (min_le_left _ _).trans (measure_mono (image_mono h))
  · exact (min_le_right _ _).trans (measure_mono (image_mono h))

end LatticeProb

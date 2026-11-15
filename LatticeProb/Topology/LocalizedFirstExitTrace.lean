import Mathlib

/-! # First-exit traces in localized curve segments -/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb

/-- A segment containing the root and escaping a set contains the trace up to
one of the first exits from that set, forward or backward from the root.
The displayed infimum or supremum can be a default value if that side never
exits; the alternative containing an escaping time is always well-defined. -/
theorem first_exit_trace_subset_of_not_subset {X : Type*} (η : ℝ → X) (U : Set X)
    {t₀ a b : ℝ}
    (ha : a ≤ t₀) (hb : t₀ ≤ b) (hescape : ¬ η '' Icc a b ⊆ U) :
    η '' Icc (sSup {t : ℝ | t ≤ t₀ ∧ η t ∉ U}) t₀ ⊆ η '' Icc a b ∨
      η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ U}) ⊆ η '' Icc a b := by
  obtain ⟨x, hx, hxU⟩ := not_subset.mp hescape
  obtain ⟨u, hu, rfl⟩ := hx
  by_cases hut : u ≤ t₀
  · left
    have hsup : u ≤ sSup {t : ℝ | t ≤ t₀ ∧ η t ∉ U} :=
      le_csSup ⟨t₀, fun _ ht => ht.1⟩ ⟨hut, hxU⟩
    exact image_mono (Icc_subset_Icc (hu.1.trans hsup) hb)
  · right
    have hinf : sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ U} ≤ u :=
      csInf_le ⟨t₀, fun _ ht => ht.1⟩ ⟨le_of_not_ge hut, hxU⟩
    exact image_mono (Icc_subset_Icc ha (hinf.trans hu.2))

/-- The measure of a segment containing the root and escaping a set is at
least the smaller measure of the two first-exit traces. -/
theorem min_first_exit_trace_measure_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (η : ℝ → X) (U : Set X) {t₀ a b : ℝ}
    (ha : a ≤ t₀) (hb : t₀ ≤ b) (hescape : ¬ η '' Icc a b ⊆ U) :
    min (μ (η '' Icc (sSup {t : ℝ | t ≤ t₀ ∧ η t ∉ U}) t₀))
        (μ (η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ U}))) ≤
      μ (η '' Icc a b) := by
  rcases first_exit_trace_subset_of_not_subset η U ha hb hescape with h | h
  · exact (min_le_left _ _).trans (measure_mono h)
  · exact (min_le_right _ _).trans (measure_mono h)

end LatticeProb

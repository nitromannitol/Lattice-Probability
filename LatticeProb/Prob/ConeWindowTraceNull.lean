import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Nullity of the complement of skipped intervals -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A null skipped trace makes the complement of its skipped intervals null,
when the original curve pushes Lebesgue time forward to the given measure. -/
theorem measure_interval_complement_eq_zero_of_skipped_trace
    (f g : C(ℝ, ℂ)) (μ : Measure ℂ) (a b : ℝ) (σ τ : ℝ → ℝ)
    (hmap : volume.map f = μ)
    (htrace : μ (g '' Icc a b) = 0)
    (hends : ∀ t ∈ Icc a b, σ t ≤ t ∧ t ≤ τ t ∧
      f (σ t) = g t ∧ f (τ t) = g t) :
    volume (Icc a b \ ⋃ t ∈ Icc a b, Ioo (σ t) (τ t)) = 0 := by
  have hcompact : IsCompact (g '' Icc a b) := isCompact_Icc.image g.continuous
  have hpre : volume (f ⁻¹' (g '' Icc a b)) = 0 := by
    rw [← Measure.map_apply f.continuous.measurable hcompact.measurableSet, hmap]
    exact htrace
  apply measure_mono_null _ hpre
  intro t ht
  have hnot : t ∉ Ioo (σ t) (τ t) := by
    intro hin
    exact ht.2 (mem_iUnion.2 ⟨t, mem_iUnion.2 ⟨ht.1, hin⟩⟩)
  obtain ⟨hst, hte, hs, he⟩ := hends t ht.1
  have heq : f t = g t := by
    by_cases hst' : σ t = t
    · simpa only [hst'] using hs
    · have hlt : σ t < t := lt_of_le_of_ne hst hst'
      have : t = τ t := le_antisymm hte (le_of_not_gt (fun h => hnot ⟨hlt, h⟩))
      simpa only [← this] using he
  exact ⟨t, ht.1, heq.symm⟩

end LatticeProb

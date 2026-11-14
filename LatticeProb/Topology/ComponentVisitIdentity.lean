import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Visit times of a measure-parametrized curve -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- If the image of a time interval is the closure of an open set, the curve pushes
Lebesgue measure forward to the spatial measure, the frontier is null, and the interval
and its image have equal mass, then visits to the open set occur almost everywhere
exactly during that interval. -/
theorem ae_visit_open_eq_interval
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (U : Set E) (a b : ℝ)
    (hη : Measurable η) (hmap : Measure.map η volume = μ)
    (hU : IsOpen U) (hfrontier : μ (frontier U) = 0)
    (himage : η '' Icc a b = closure U)
    (hmass : μ (η '' Icc a b) = volume (Icc a b)) :
    ∀ᵐ t ∂volume, η t ∈ U ↔ t ∈ Ioo a b := by
  have hclosed : MeasurableSet (closure U) := isClosed_closure.measurableSet
  have hpre : volume (η ⁻¹' closure U) = volume (Icc a b) := by
    rw [← Measure.map_apply hη hclosed, hmap, ← himage, hmass]
  have hsubset : Icc a b ⊆ η ⁻¹' closure U := by
    intro t ht
    exact himage ▸ ⟨t, ht, rfl⟩
  have hfinite : volume (η ⁻¹' closure U) ≠ ∞ := by
    rw [hpre, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have heq : Icc a b =ᵐ[volume] η ⁻¹' closure U :=
    ae_eq_of_subset_of_measure_ge hsubset (le_of_eq hpre)
      measurableSet_Icc.nullMeasurableSet hfinite
  have hnull : volume (η ⁻¹' frontier U) = 0 := by
    rw [← Measure.map_apply hη isClosed_frontier.measurableSet, hmap, hfrontier]
  have hfront : ∀ᵐ t ∂volume, η t ∉ frontier U := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [heq, hfront, (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t ht hf hi
  simp only [mem_preimage] at ht
  have hu : η t ∈ U ↔ η t ∈ closure U := by
    constructor
    · intro hx
      exact subset_closure hx
    · intro hc
      by_contra hn
      apply hf
      rw [hU.frontier_eq]
      exact ⟨hc, hn⟩
  exact hu.trans ((iff_of_eq ht.symm).trans (iff_of_eq hi.symm))

end LatticeProb

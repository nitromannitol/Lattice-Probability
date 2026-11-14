import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # Frontiers of measure-parametrized curve segments -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- A measure-parametrized curve segment has null frontier when its image has the
mass of the time interval and almost every interior time visits its interior. -/
theorem measure_frontier_curve_segment_eq_zero
    {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    (η : ℝ → E) (μ : Measure E) (a b : ℝ)
    (hη : Continuous η) (hmap : Measure.map η volume = μ)
    (hmass : μ (η '' Icc a b) = volume (Icc a b))
    (hinterior : ∀ᵐ t ∂volume.restrict (Ioo a b),
      η t ∈ interior (η '' Icc a b)) :
    μ (frontier (η '' Icc a b)) = 0 := by
  let K := η '' Icc a b
  have hclosed : IsClosed K := (isCompact_Icc.image hη).isClosed
  have hpre : volume (η ⁻¹' K) = volume (Icc a b) := by
    rw [← Measure.map_apply hη.measurable hclosed.measurableSet, hmap]
    exact hmass
  have hsubset : Icc a b ⊆ η ⁻¹' K := fun t ht => ⟨t, ht, rfl⟩
  have hfinite : volume (η ⁻¹' K) ≠ ∞ := by
    rw [hpre, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have heq : Icc a b =ᵐ[volume] η ⁻¹' K :=
    ae_eq_of_subset_of_measure_ge hsubset (le_of_eq hpre)
      measurableSet_Icc.nullMeasurableSet hfinite
  have hvisit : ∀ᵐ t ∂volume, t ∈ Ioo a b → η t ∈ interior K :=
    (ae_restrict_iff' measurableSet_Ioo).mp hinterior
  have hnot : ∀ᵐ t ∂volume, η t ∉ frontier K := by
    filter_upwards [heq, hvisit, (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b))] with t ht hv hi
    intro hf
    have hK : η t ∈ K := hclosed.closure_eq ▸ frontier_subset_closure hf
    have hIcc : t ∈ Icc a b := (iff_of_eq ht).mpr hK
    have hIoo : t ∈ Ioo a b := (iff_of_eq hi).mpr hIcc
    change η t ∈ closure K \ interior K at hf
    exact hf.2 (hv hIoo)
  have hzero : volume (η ⁻¹' frontier K) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr hnot
  rw [← Measure.map_apply hη.measurable isClosed_frontier.measurableSet, hmap] at hzero
  exact hzero

end LatticeProb

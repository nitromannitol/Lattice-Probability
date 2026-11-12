import Mathlib

/-!
# Intensity of a family of measures: from sets to nonnegative functions

Let `ν : Ω → Measure Y` be a family of measures indexed by a probability space (not assumed to be a kernel) and
`ρ` a measure on `Y`.  If for every measurable set `S` the map `ω ↦ ν ω S` is almost everywhere measurable with
`∫⁻ ω, ν ω S ∂P = ρ S`, then for every measurable `f : Y → [0, ∞]` the map `ω ↦ ∫⁻ y, f y ∂ν ω` is almost
everywhere measurable and `∫⁻ ω, ∫⁻ y, f y ∂ν ω ∂P = ∫⁻ y, f y ∂ρ`.  The proof is the standard induction over
indicators, sums of functions with disjoint supports and monotone suprema.

## Main statement

* `LatticeProb.aemeasurable_and_lintegral_eq_of_forall_measurableSet`.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- **From sets to functions for a family of measures with given intensity.** If, for every measurable set `S`,
`ω ↦ ν ω S` is almost everywhere measurable with `∫⁻ ω, ν ω S ∂P = ρ S`, then for every measurable
`f : Y → [0, ∞]`, `ω ↦ ∫⁻ y, f y ∂ν ω` is almost everywhere measurable and
`∫⁻ ω, ∫⁻ y, f y ∂ν ω ∂P = ∫⁻ y, f y ∂ρ`. -/
theorem aemeasurable_and_lintegral_eq_of_forall_measurableSet {Ω Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y] {P : Measure Ω} (ν : Ω → Measure Y) (ρ : Measure Y)
    (hbase : ∀ S : Set Y, MeasurableSet S →
      AEMeasurable (fun ω => ν ω S) P ∧ ∫⁻ ω, ν ω S ∂P = ρ S) :
    ∀ f : Y → ℝ≥0∞, Measurable f →
      AEMeasurable (fun ω => ∫⁻ y, f y ∂(ν ω)) P ∧ ∫⁻ ω, ∫⁻ y, f y ∂(ν ω) ∂P = ∫⁻ y, f y ∂ρ := by
  intro f hf
  refine Measurable.ennreal_induction
    (motive := fun f => AEMeasurable (fun ω => ∫⁻ y, f y ∂(ν ω)) P ∧
      ∫⁻ ω, ∫⁻ y, f y ∂(ν ω) ∂P = ∫⁻ y, f y ∂ρ) ?_ ?_ ?_ hf
  · intro c s hs
    have h := hbase s hs
    simp_rw [lintegral_indicator_const hs]
    exact ⟨h.1.const_mul c, by rw [lintegral_const_mul'' _ h.1, h.2]⟩
  · intro f g hdisj hfm hgm ihf ihg
    have hadd : ∀ ω, ∫⁻ y, (f + g) y ∂(ν ω) = ∫⁻ y, f y ∂(ν ω) + ∫⁻ y, g y ∂(ν ω) := fun ω =>
      lintegral_add_left hfm _
    simp_rw [hadd]
    exact ⟨ihf.1.add ihg.1, by rw [lintegral_add_left' ihf.1, ihf.2, ihg.2]; exact (lintegral_add_left hfm _).symm⟩
  · intro f hfm hmono ih
    have hs : ∀ ω, ∫⁻ y, ⨆ n, f n y ∂(ν ω) = ⨆ n, ∫⁻ y, f n y ∂(ν ω) := fun ω =>
      lintegral_iSup hfm hmono
    beta_reduce
    simp_rw [hs]
    refine ⟨AEMeasurable.iSup fun n => (ih n).1, ?_⟩
    rw [lintegral_iSup' (fun n => (ih n).1) (Filter.Eventually.of_forall fun ω a b hab =>
      lintegral_mono (hmono hab)), lintegral_iSup hfm hmono]
    exact iSup_congr fun n => (ih n).2

end LatticeProb

import Mathlib

/-!
# Intensity of a family of measures determined on a `π`-system

Let `ν : Ω → Measure Y` be a family of measures indexed by a probability space which is not assumed to be a
kernel (the maps `ω ↦ ν ω s` need not be measurable), and `ρ` a finite measure on `Y`.  If, for the sets `s`
of a `π`-system `Sys` generating the `σ`-algebra of `Y` and containing `univ`, the map `ω ↦ ν ω s` is almost
everywhere measurable with `∫⁻ ω, ν ω s ∂P = ρ s`, then the same holds for every measurable set.  The proof is
the `π`-`λ` theorem: the sets for which the conclusion holds are closed under complements (the total mass is
almost surely finite, being integrable) and countable disjoint unions.

## Main statement

* `LatticeProb.aemeasurable_and_lintegral_eq_of_isPiSystem`.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb

/-- **Extension from a `π`-system for a family of measures with finite mean.** If `ν : Ω → Measure Y` and a
finite measure `ρ` satisfy, for every `s` in a `π`-system `Sys` generating the `σ`-algebra of `Y` and containing
`univ`, that `ω ↦ ν ω s` is almost everywhere measurable and `∫⁻ ω, ν ω s ∂P = ρ s`, then every measurable
set has the same two properties. -/
theorem aemeasurable_and_lintegral_eq_of_isPiSystem {Ω Y : Type*} [MeasurableSpace Ω] {m : MeasurableSpace Y}
    {P : Measure Ω} (ν : Ω → Measure Y) (ρ : Measure Y) [IsFiniteMeasure ρ] {Sys : Set (Set Y)}
    (hgen : m = MeasurableSpace.generateFrom Sys) (hpi : IsPiSystem Sys) (huniv : Set.univ ∈ Sys)
    (hbase : ∀ s ∈ Sys, AEMeasurable (fun ω => ν ω s) P ∧ ∫⁻ ω, ν ω s ∂P = ρ s) :
    ∀ S, MeasurableSet S → AEMeasurable (fun ω => ν ω S) P ∧ ∫⁻ ω, ν ω S ∂P = ρ S := by
  have hU := hbase _ huniv
  have hUfin : ∀ᵐ ω ∂P, ν ω Set.univ < ∞ :=
    ae_lt_top' hU.1 (by rw [hU.2]; exact measure_ne_top ρ _)
  intro S hS
  induction S, hS using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic t ht => exact hbase t ht
  | compl t htm ih =>
    have hae : (fun ω => ν ω tᶜ) =ᵐ[P] fun ω => ν ω Set.univ - ν ω t := by
      filter_upwards [hUfin] with ω hω
      exact measure_compl htm (ne_top_of_le_ne_top hω.ne (measure_mono (Set.subset_univ t)))
    have hle : (fun ω => ν ω t) ≤ᵐ[P] fun ω => ν ω Set.univ :=
      Filter.Eventually.of_forall fun ω => measure_mono (Set.subset_univ t)
    refine ⟨(hU.1.sub ih.1).congr hae.symm, ?_⟩
    rw [lintegral_congr_ae hae, lintegral_sub' ih.1 (by rw [ih.2]; exact measure_ne_top ρ _) hle, hU.2, ih.2,
      measure_compl htm (measure_ne_top ρ _)]
  | iUnion f hdisj hfm ih =>
    have hae : ∀ ω, ν ω (⋃ i, f i) = ∑' i, ν ω (f i) := fun ω => measure_iUnion hdisj hfm
    simp_rw [hae]
    exact ⟨AEMeasurable.tsum fun i => (ih i).1, by
      rw [lintegral_tsum fun i => (ih i).1, measure_iUnion hdisj hfm]
      exact tsum_congr fun i => (ih i).2⟩

end LatticeProb

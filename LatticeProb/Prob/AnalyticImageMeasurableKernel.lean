import LatticeProb.Prob.AnalyticUniversalMeasurable

/-!
# A measurable kernel of the image of a measurable set

Let `X` be a standard Borel space with a finite measure `P`, `Y` a second-countable, metrizable topological space
with a Borel-compatible σ-algebra, `f : X → Y` measurable and `W ⊆ X` measurable. The image `f '' W` need not be
measurable, but it is analytic, hence null-measurable for the image measure `P.map f`. So it contains a measurable
set `A` whose preimage covers `W` up to a `P`-null set:

* `exists_measurableSet_subset_image_measure_diff_preimage_eq_zero`: `∃ A ⊆ f '' W`, `MeasurableSet A` and
  `P (W \ f ⁻¹' A) = 0`;
* `exists_measurableSet_subset_image_measure_preimage_compl_eq_zero`: if moreover `W` has full measure, then
  `P (f ⁻¹' Aᶜ) = 0`.

Every point of such an `A` is the image of a point of `W`. This transfers a property that holds on a set of full
measure in `X` to a measurable set of full image measure in `Y` on which the property holds at some preimage.
-/

open MeasureTheory Set

namespace LatticeProb

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace.PseudoMetrizableSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

/-- **A measurable kernel of the image of a measurable set.** For a finite measure `P` on a standard Borel space, a
measurable map `f` into a second-countable metrizable space and a measurable set `W`, there is a measurable set
`A ⊆ f '' W` with `P (W \ f ⁻¹' A) = 0`. -/
theorem exists_measurableSet_subset_image_measure_diff_preimage_eq_zero (P : Measure X) [IsFiniteMeasure P]
    {f : X → Y} (hf : Measurable f) {W : Set X} (hW : MeasurableSet W) :
    ∃ A ⊆ f '' W, MeasurableSet A ∧ P (W \ f ⁻¹' A) = 0 := by
  have hN : NullMeasurableSet (f '' W) (P.map f) :=
    LatticeProb.AnalyticSet.nullMeasurableSet (P.map f) (hW.analyticSet_image hf)
  obtain ⟨A, hAW, hA, hAe⟩ := hN.exists_measurable_subset_ae_eq
  refine ⟨A, hAW, hA, measure_mono_null (t := f ⁻¹' (f '' W \ A)) ?_ (nonpos_iff_eq_zero.1
    ((Measure.le_map_apply hf.aemeasurable _).trans_eq (ae_eq_set.1 hAe).2))⟩
  intro x hx
  exact ⟨mem_image_of_mem f hx.1, hx.2⟩

/-- **A measurable kernel of the image of a set of full measure.** For a finite measure `P` on a standard Borel
space, a measurable map `f` into a second-countable metrizable space and a measurable set `W` of full measure, there
is a measurable set `A ⊆ f '' W` with `P (f ⁻¹' Aᶜ) = 0`. -/
theorem exists_measurableSet_subset_image_measure_preimage_compl_eq_zero (P : Measure X) [IsFiniteMeasure P]
    {f : X → Y} (hf : Measurable f) {W : Set X} (hW : MeasurableSet W) (hWc : P Wᶜ = 0) :
    ∃ A ⊆ f '' W, MeasurableSet A ∧ P (f ⁻¹' Aᶜ) = 0 := by
  obtain ⟨A, hAW, hA, h0⟩ := exists_measurableSet_subset_image_measure_diff_preimage_eq_zero P hf hW
  refine ⟨A, hAW, hA, measure_mono_null ?_ (measure_union_null hWc h0)⟩
  intro x hx
  by_cases hxW : x ∈ W
  · exact Or.inr ⟨hxW, hx⟩
  · exact Or.inl hxW

end LatticeProb

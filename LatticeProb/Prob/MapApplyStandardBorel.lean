import LatticeProb.Prob.AnalyticUniversalMeasurable

/-!
# Pushforward of arbitrary sets from a standard Borel space

Let `P` be a finite measure on a standard Borel space `Ω` and `g : Ω → Y` a measurable map into a standard Borel
space (or a second-countable metrizable space with a Borel σ-algebra). For every set `B ⊆ Y`, measurable or not,
the outer measure of `B` under the law `P.map g` equals the outer measure of `g ⁻¹' B` under `P`.

The inequality `P (g ⁻¹' B) ≤ P.map g B` holds for every measurable map (`MeasureTheory.Measure.le_map_apply`). For
the reverse inequality take a measurable hull `M ⊇ g ⁻¹' B`. The image `g '' Mᶜ` is analytic and disjoint from `B`,
analytic sets are null-measurable for every finite Borel measure (`LatticeProb.AnalyticSet.nullMeasurableSet`), and
the preimage of the complement of `g '' Mᶜ` lies in `M`.

Consequence (transfer of bounds between realizations, `measure_preimage_le_of_map_eq`): if `g₁ : Ω₁ → Y` and
`g : Ω → Y` have the same law and `Ω` is standard Borel, then `P₁ (g₁ ⁻¹' B) ≤ P (g ⁻¹' B)` for every `B ⊆ Y`. No
measurability of `B` and no assumption on the measurable space `Ω₁` is needed.
-/

open MeasureTheory Set

namespace LatticeProb

section Topological

variable {Ω Y : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace.PseudoMetrizableSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- **Pushforward outer measure is at most the preimage outer measure.** For a finite measure `P` on a standard
Borel space, a measurable map `g` into a second-countable metrizable space with a Borel σ-algebra, and an
arbitrary set `B`, `P.map g B ≤ P (g ⁻¹' B)`. -/
theorem map_apply_le_measure_preimage (P : Measure Ω) [IsFiniteMeasure P] {g : Ω → Y}
    (hg : Measurable g) (B : Set Y) : P.map g B ≤ P (g ⁻¹' B) := by
  set M := toMeasurable P (g ⁻¹' B)
  have hMm : MeasurableSet M := measurableSet_toMeasurable P _
  have hA : AnalyticSet (g '' Mᶜ) := hMm.compl.analyticSet_image hg
  have hnull : NullMeasurableSet (g '' Mᶜ)ᶜ (P.map g) :=
    (AnalyticSet.nullMeasurableSet (P.map g) hA).compl
  have hB : B ⊆ (g '' Mᶜ)ᶜ := by
    rintro y hy ⟨ω, hω, rfl⟩
    exact hω (subset_toMeasurable P _ hy)
  calc P.map g B ≤ P.map g (g '' Mᶜ)ᶜ := measure_mono hB
    _ = P (g ⁻¹' (g '' Mᶜ)ᶜ) := Measure.map_apply₀ hg.aemeasurable hnull
    _ ≤ P M := by
        refine measure_mono fun ω hω => ?_
        by_contra h
        exact hω ⟨ω, h, rfl⟩
    _ = P (g ⁻¹' B) := measure_toMeasurable _

/-- **Pushforward of arbitrary sets.** For a finite measure `P` on a standard Borel space, a measurable map `g`
into a second-countable metrizable space with a Borel σ-algebra, and an arbitrary set `B`,
`P.map g B = P (g ⁻¹' B)` (outer measures). -/
theorem map_apply_eq_measure_preimage (P : Measure Ω) [IsFiniteMeasure P] {g : Ω → Y}
    (hg : Measurable g) (B : Set Y) : P.map g B = P (g ⁻¹' B) :=
  le_antisymm (map_apply_le_measure_preimage P hg B) (Measure.le_map_apply hg.aemeasurable B)

end Topological

section StandardBorel

variable {Ω Y : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace Y] [StandardBorelSpace Y]

/-- **Pushforward of arbitrary sets between standard Borel spaces.** For a finite measure `P` on a standard Borel
space, a measurable map `g` into a standard Borel space, and an arbitrary set `B`, `P.map g B = P (g ⁻¹' B)`
(outer measures). -/
theorem map_apply_eq_measure_preimage_of_standardBorel (P : Measure Ω) [IsFiniteMeasure P]
    {g : Ω → Y} (hg : Measurable g) (B : Set Y) : P.map g B = P (g ⁻¹' B) := by
  let := upgradeStandardBorel Y
  exact map_apply_eq_measure_preimage P hg B

/-- **Transfer of an outer-measure bound between two realizations of a law.** Let `g₁ : Ω₁ → Y` be almost
everywhere measurable for `P₁` on an arbitrary measurable space, and `g : Ω → Y` measurable on a standard Borel
space with a finite measure `P`, with the same law: `P₁.map g₁ = P.map g`, `Y` standard Borel. Then for every set
`B ⊆ Y`, measurable or not, `P₁ (g₁ ⁻¹' B) ≤ P (g ⁻¹' B)`. -/
theorem measure_preimage_le_of_map_eq {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {g₁ : Ω₁ → Y} (hg₁ : AEMeasurable g₁ P₁) (P : Measure Ω) [IsFiniteMeasure P] {g : Ω → Y}
    (hg : Measurable g) (hlaw : P₁.map g₁ = P.map g) (B : Set Y) :
    P₁ (g₁ ⁻¹' B) ≤ P (g ⁻¹' B) :=
  calc P₁ (g₁ ⁻¹' B) ≤ P₁.map g₁ B := Measure.le_map_apply hg₁ B
    _ = P.map g B := by rw [hlaw]
    _ = P (g ⁻¹' B) := map_apply_eq_measure_preimage_of_standardBorel P hg B

/-- **Equality of outer measures of preimages for two realizations of a law**, both on standard Borel spaces with
finite measures: if `P₁.map g₁ = P₂.map g₂` then `P₁ (g₁ ⁻¹' B) = P₂ (g₂ ⁻¹' B)` for every `B ⊆ Y`. -/
theorem measure_preimage_eq_of_map_eq {Ω₁ : Type*} [MeasurableSpace Ω₁] [StandardBorelSpace Ω₁]
    {P₁ : Measure Ω₁} [IsFiniteMeasure P₁] {g₁ : Ω₁ → Y} (hg₁ : Measurable g₁) (P : Measure Ω)
    [IsFiniteMeasure P] {g : Ω → Y} (hg : Measurable g) (hlaw : P₁.map g₁ = P.map g) (B : Set Y) :
    P₁ (g₁ ⁻¹' B) = P (g ⁻¹' B) :=
  le_antisymm (measure_preimage_le_of_map_eq hg₁.aemeasurable P hg hlaw B)
    (measure_preimage_le_of_map_eq hg.aemeasurable P₁ hg₁ hlaw.symm B)

end StandardBorel

end LatticeProb

/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Tightness on a product space from tight marginals

A set of finite measures on `X × Y` whose two marginals form tight sets is tight: if `K₁ ⊆ X` and
`K₂ ⊆ Y` are compact sets whose complements carry mass at most `ε / 2` under every first, resp.
second, marginal, then `K₁ ×ˢ K₂` is compact and its complement carries mass at most `ε` under every
measure of the set.

* `LatticeProb.isTightMeasureSet_prod`: the statement for a set of measures on `X × Y`.
* `LatticeProb.isTightMeasureSet_map_pair`: the statement for the laws of pairs of random elements
  `(X i, Y i)` of a family of probability spaces.
-/

open Filter Topology Set MeasureTheory

open scoped ENNReal

namespace LatticeProb

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X]
  [MeasurableSpace Y]

/-- **Tightness from tight marginals.**  If the sets of first and second marginals of a set `S` of
measures on `X × Y` are tight, then `S` is tight. -/
theorem isTightMeasureSet_prod {S : Set (Measure (X × Y))}
    (h1 : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.fst) '' S))
    (h2 : IsTightMeasureSet ((fun μ : Measure (X × Y) => μ.map Prod.snd) '' S)) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h1 h2 ⊢
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨K₁, hK₁, hK₁m⟩ := h1 (e / 2) he2
  obtain ⟨K₂, hK₂, hK₂m⟩ := h2 (e / 2) he2
  refine ⟨K₁ ×ˢ K₂, hK₁.prod hK₂, fun μ hμ => ?_⟩
  have hsub : (K₁ ×ˢ K₂)ᶜ ⊆ Prod.fst ⁻¹' K₁ᶜ ∪ Prod.snd ⁻¹' K₂ᶜ := by
    intro p hp
    by_contra h
    simp only [mem_union, mem_preimage, mem_compl_iff, not_or, not_not] at h
    exact hp ⟨h.1, h.2⟩
  calc μ (K₁ ×ˢ K₂)ᶜ ≤ μ (Prod.fst ⁻¹' K₁ᶜ ∪ Prod.snd ⁻¹' K₂ᶜ) := measure_mono hsub
    _ ≤ μ (Prod.fst ⁻¹' K₁ᶜ) + μ (Prod.snd ⁻¹' K₂ᶜ) := measure_union_le _ _
    _ ≤ μ.map Prod.fst K₁ᶜ + μ.map Prod.snd K₂ᶜ :=
        add_le_add (Measure.le_map_apply measurable_fst.aemeasurable _)
          (Measure.le_map_apply measurable_snd.aemeasurable _)
    _ ≤ e / 2 + e / 2 := add_le_add (hK₁m _ ⟨μ, hμ, rfl⟩) (hK₂m _ ⟨μ, hμ, rfl⟩)
    _ = e := ENNReal.add_halves e

/-- **Tightness of the laws of pairs.**  Let `X i, Y i` be random elements, with values in `A`
and `B`, of the probability spaces `(Ω, μ i)`.  If the laws of the `X i` form a tight set and so do
the laws of the `Y i`, then the laws of the pairs `(X i, Y i)` form a tight set. -/
theorem isTightMeasureSet_map_pair {A B Ω ι : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Ω] (μ : ι → Measure Ω)
    (X : ι → Ω → A) (Y : ι → Ω → B) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXt : IsTightMeasureSet {ν : Measure A | ∃ i, ν = (μ i).map (X i)})
    (hYt : IsTightMeasureSet {ν : Measure B | ∃ i, ν = (μ i).map (Y i)}) :
    IsTightMeasureSet {ν : Measure (A × B) | ∃ i, ν = (μ i).map fun ω => (X i ω, Y i ω)} := by
  refine isTightMeasureSet_prod (hXt.subset ?_) (hYt.subset ?_)
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    beta_reduce
    rw [Measure.map_map measurable_fst ((hX i).prodMk (hY i))]
    rfl
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    beta_reduce
    rw [Measure.map_map measurable_snd ((hX i).prodMk (hY i))]
    rfl

end LatticeProb

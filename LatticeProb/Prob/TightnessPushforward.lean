/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Tightness is preserved by continuous images

If `S` is a tight set of measures on `X` and `f : X → Y` is continuous and measurable, with `Y`
Hausdorff and its open sets measurable, then the set of image measures `μ.map f`, `μ ∈ S`, is tight
on `Y`: if `K` is compact with `μ Kᶜ ≤ ε` for all `μ ∈ S`, then `f '' K` is compact, hence closed,
and `f⁻¹ (f '' K)ᶜ ⊆ Kᶜ`.

* `LatticeProb.isTightMeasureSet_image_map`: the statement for a set of measures.
* `LatticeProb.isTightMeasureSet_map_comp`: the statement for the laws of a family of random elements
  composed with a continuous map.
-/

open Filter Topology Set MeasureTheory

open scoped ENNReal

namespace LatticeProb

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X]
  [MeasurableSpace Y]

/-- **Pushforward of a tight set under a continuous map.** -/
theorem isTightMeasureSet_image_map [T2Space Y] [OpensMeasurableSpace Y] {S : Set (Measure X)}
    (hS : IsTightMeasureSet S) {f : X → Y} (hf : Continuous f) (hfm : Measurable f) :
    IsTightMeasureSet ((fun μ : Measure X => μ.map f) '' S) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hS ⊢
  intro e he
  obtain ⟨K, hK, hKm⟩ := hS e he
  have hK' : IsCompact (f '' K) := hK.image hf
  refine ⟨f '' K, hK', ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  rw [Measure.map_apply hfm hK'.isClosed.measurableSet.compl]
  refine le_trans (measure_mono ?_) (hKm μ hμ)
  intro x hx hxK
  exact hx ⟨x, hxK, rfl⟩

/-- **Tightness of the laws of the composition with a continuous map.**  If the laws of random
elements `X i` of `(Ω, μ i)` with values in `A` form a tight set, then so do the laws of `f ∘ X i`
for a continuous measurable `f : A → B`. -/
theorem isTightMeasureSet_map_comp {A B Ω ι : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Ω] [T2Space B]
    [OpensMeasurableSpace B] (μ : ι → Measure Ω) (X : ι → Ω → A) (hX : ∀ i, Measurable (X i))
    (hXt : IsTightMeasureSet {ν : Measure A | ∃ i, ν = (μ i).map (X i)}) {f : A → B}
    (hf : Continuous f) (hfm : Measurable f) :
    IsTightMeasureSet {ν : Measure B | ∃ i, ν = (μ i).map fun ω => f (X i ω)} := by
  refine (isTightMeasureSet_image_map hXt hf hfm).subset ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨_, ⟨i, rfl⟩, ?_⟩
  beta_reduce
  rw [Measure.map_map hfm (hX i)]
  rfl

end LatticeProb

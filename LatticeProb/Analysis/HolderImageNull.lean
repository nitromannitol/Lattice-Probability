import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hölder images of small sets of times are Lebesgue-null

Let `X : ℝ → ℝ` and let `Z ⊆ ℝ` be a set of times. The set of levels `X '' Z` is Lebesgue-null in two situations:
* `X` is locally `α`-Hölder on `Z` and the Hausdorff dimension of `Z` is at most `d` with `d / α < 1`. Then
  `dimH (X '' Z) ≤ dimH Z / α < 1` (`dimH_image_le_of_locally_holder_on`), and on `ℝ` the one-dimensional Hausdorff
  measure is Lebesgue measure (`hausdorffMeasure_real`), so `X '' Z` is null (`hausdorffMeasure_of_dimH_lt`).
* `Z` is countable.

The complement of a Lebesgue-null set of levels meets every nonempty open interval, so the levels outside `X '' Z`
are dense.

The dimension bound on `Z`, its countability and the local Hölder continuity of `X` enter only as hypotheses.

## Main results
* `volume_image_eq_zero_of_dimH`, `volume_image_eq_zero_of_countable`: the two cases.
* `volume_image_eq_zero_of_countable_or_dimH`, `volume_image_union_eq_zero`: the combined form, for one path and for
  both coordinates `L`, `R` of a pair of paths.
* `exists_mem_Ioo_notMem_of_volume_eq_zero`, `exists_mem_Ioo_notMem_image`: levels outside a null set are dense.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- A locally `α`-Hölder image of a set of Hausdorff dimension at most `d`, with `d / α < 1`, has Hausdorff dimension
less than `1`. -/
theorem dimH_image_lt_one {X : ℝ → ℝ} {Z : Set ℝ} {α : ℝ≥0} (hα : 0 < α)
    (hX : ∀ x ∈ Z, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[Z] x, HolderOnWith C α X t) {d : ℝ≥0∞} (hZ : dimH Z ≤ d)
    (hd : d / α < 1) : dimH (X '' Z) < 1 :=
  calc dimH (X '' Z) ≤ dimH Z / α := dimH_image_le_of_locally_holder_on hα hX
    _ ≤ d / α := ENNReal.div_le_div_right hZ _
    _ < 1 := hd

/-- **Hölder image of a set of small dimension.** If `X` is locally `α`-Hölder on `Z` and `dimH Z ≤ d` with
`d / α < 1`, then `X '' Z` is Lebesgue-null. -/
theorem volume_image_eq_zero_of_dimH {X : ℝ → ℝ} {Z : Set ℝ} {α : ℝ≥0} (hα : 0 < α)
    (hX : ∀ x ∈ Z, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[Z] x, HolderOnWith C α X t) {d : ℝ≥0∞} (hZ : dimH Z ≤ d)
    (hd : d / α < 1) : volume (X '' Z) = 0 := by
  have h₁ : dimH (X '' Z) < ((1 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_one]
    exact dimH_image_lt_one hα hX hZ hd
  have h₂ := hausdorffMeasure_of_dimH_lt h₁
  rw [NNReal.coe_one, hausdorffMeasure_real] at h₂
  exact h₂

/-- **Image of a countable set.** For any `X`, the image of a countable set of times is Lebesgue-null. -/
theorem volume_image_eq_zero_of_countable (X : ℝ → ℝ) {Z : Set ℝ} (hZ : Z.Countable) :
    volume (X '' Z) = 0 :=
  (hZ.image X).measure_zero volume

/-- **Combined form.** If `X` is locally `α`-Hölder and `Z` is countable or has Hausdorff dimension at most `d` with
`d / α < 1`, then `X '' Z` is Lebesgue-null. -/
theorem volume_image_eq_zero_of_countable_or_dimH {X : ℝ → ℝ} {Z : Set ℝ} {α : ℝ≥0} (hα : 0 < α)
    (hX : ∀ x, ∃ C : ℝ≥0, ∃ t ∈ 𝓝 x, HolderOnWith C α X t)
    (hZ : Z.Countable ∨ ∃ d : ℝ≥0∞, dimH Z ≤ d ∧ d / α < 1) : volume (X '' Z) = 0 := by
  rcases hZ with hZ | ⟨d, hZd, hd⟩
  · exact volume_image_eq_zero_of_countable X hZ
  · refine volume_image_eq_zero_of_dimH hα (fun x _ => ?_) hZd hd
    obtain ⟨C, t, ht, hCt⟩ := hX x
    exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hCt⟩

/-- **Combined form for both coordinates.** If `L` and `R` are locally `α`-Hölder and `Z` is countable or has
Hausdorff dimension at most `d` with `d / α < 1`, then the levels `L '' Z ∪ R '' Z` form a Lebesgue-null set. -/
theorem volume_image_union_eq_zero {L R : ℝ → ℝ} {Z : Set ℝ} {α : ℝ≥0} (hα : 0 < α)
    (hL : ∀ x, ∃ C : ℝ≥0, ∃ t ∈ 𝓝 x, HolderOnWith C α L t)
    (hR : ∀ x, ∃ C : ℝ≥0, ∃ t ∈ 𝓝 x, HolderOnWith C α R t)
    (hZ : Z.Countable ∨ ∃ d : ℝ≥0∞, dimH Z ≤ d ∧ d / α < 1) : volume (L '' Z ∪ R '' Z) = 0 :=
  measure_union_null (volume_image_eq_zero_of_countable_or_dimH hα hL hZ)
    (volume_image_eq_zero_of_countable_or_dimH hα hR hZ)

/-- Every nonempty open interval contains a level outside a Lebesgue-null set. -/
theorem exists_mem_Ioo_notMem_of_volume_eq_zero {N : Set ℝ} (hN : volume N = 0) {a b : ℝ} (hab : a < b) :
    ∃ ℓ ∈ Ioo a b, ℓ ∉ N := by
  by_contra h
  have hsub : Ioo a b ⊆ N := fun ℓ hℓ => by
    by_contra hn
    exact h ⟨ℓ, hℓ, hn⟩
  have h₁ : volume (Ioo a b) ≤ volume N := measure_mono hsub
  rw [hN, Real.volume_Ioo, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h₁
  linarith

/-- **The levels outside the exceptional levels are dense.** Under the hypotheses of `volume_image_union_eq_zero`,
every nonempty open interval contains a level that is neither in `L '' Z` nor in `R '' Z`. -/
theorem exists_mem_Ioo_notMem_image {L R : ℝ → ℝ} {Z : Set ℝ} {α : ℝ≥0} (hα : 0 < α)
    (hL : ∀ x, ∃ C : ℝ≥0, ∃ t ∈ 𝓝 x, HolderOnWith C α L t)
    (hR : ∀ x, ∃ C : ℝ≥0, ∃ t ∈ 𝓝 x, HolderOnWith C α R t)
    (hZ : Z.Countable ∨ ∃ d : ℝ≥0∞, dimH Z ≤ d ∧ d / α < 1) {a b : ℝ} (hab : a < b) :
    ∃ ℓ ∈ Ioo a b, ℓ ∉ L '' Z ∧ ℓ ∉ R '' Z := by
  obtain ⟨ℓ, hℓ, hn⟩ :=
    exists_mem_Ioo_notMem_of_volume_eq_zero (volume_image_union_eq_zero hα hL hR hZ) hab
  exact ⟨ℓ, hℓ, fun h => hn (mem_union_left _ h), fun h => hn (mem_union_right _ h)⟩

end LatticeProb

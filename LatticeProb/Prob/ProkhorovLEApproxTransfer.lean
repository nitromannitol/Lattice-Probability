import LatticeProb.Prob.KernelProkhorovChain

/-!
# Transfer of a one-sided Prokhorov bound through approximating skeletons

Let `μ` and `ν` be measures on `Ω₁` and `Ω₂`, and let `H₁ : Ω₁ → E`, `H₂ : Ω₂ → E` be measurable
skeleton maps into a pseudometric space `E` (for instance, the positions of a path at finitely many
knot times) whose laws satisfy the one-sided Prokhorov relation `ProkhorovLE (μ.map H₁) (ν.map H₂) δ e`.
Let `P₁ : Ω₁ → Y` and `P₂ : Ω₂ → Y` be maps into an arbitrary type `Y` carrying an extended distance
`d` satisfying the triangle inequality (for instance, a distance between curves modulo time
parametrization), and let `Φ : E → Y` be `1`-Lipschitz for `d` (a reconstruction of a curve from its
skeleton). If `P₁` is within `a` of `Φ ∘ H₁` on `G₁` and `P₂` is within `a'` of `Φ ∘ H₂` on `G₂`, then
for every set `A ⊆ Y` (no measurability assumed)
`μ (P₁ ⁻¹' A) ≤ ν {ω | ∃ f ∈ A, d (P₂ ω) f < a' + δ + a} + e + μ G₁ᶜ + ν G₂ᶜ`.

This is the measure-theoretic step that turns a comparison of skeleton laws into a one-sided
Prokhorov-type comparison of the laws of the curves themselves.

## Main statements

* `LatticeProb.isOpen_setOf_exists_lt_of_lipschitz`: the preimage under a `1`-Lipschitz `Φ` of the
  open `a`-neighbourhood of any set is open.
* `LatticeProb.measure_preimage_le_of_prokhorovLE_of_approx`: the transfer bound.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

variable {E Y : Type*} [PseudoMetricSpace E]

/-- For an extended distance `d` on `Y` with the triangle inequality and a map `Φ : E → Y` which is
`1`-Lipschitz from `edist` to `d`, the set of points whose image is within `d`-distance `< a` of
some point of `A` is open, for every `A ⊆ Y`. -/
theorem isOpen_setOf_exists_lt_of_lipschitz {d : Y → Y → ℝ≥0∞}
    (hd : ∀ x y z, d x z ≤ d x y + d y z) {Φ : E → Y} (hΦ : ∀ x x', d (Φ x) (Φ x') ≤ edist x x')
    (A : Set Y) (a : ℝ≥0∞) : IsOpen {x | ∃ f ∈ A, d (Φ x) f < a} := by
  refine EMetric.isOpen_iff.mpr fun x hx => ?_
  obtain ⟨f, hfA, hxf⟩ := hx
  have hne : d (Φ x) f ≠ ∞ := ne_top_of_lt hxf
  refine ⟨a - d (Φ x) f, tsub_pos_of_lt hxf, fun x' hx' => ⟨f, hfA, ?_⟩⟩
  have h1 : edist x' x < a - d (Φ x) f := hx'
  calc d (Φ x') f ≤ d (Φ x') (Φ x) + d (Φ x) f := hd _ _ _
    _ ≤ edist x' x + d (Φ x) f := by gcongr; exact hΦ x' x
    _ < a - d (Φ x) f + d (Φ x) f := ENNReal.add_lt_add_right hne h1
    _ = a := tsub_add_cancel_of_le hxf.le

variable [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Transfer of a one-sided Prokhorov bound from skeletons to curves.** If the skeleton laws
satisfy `ProkhorovLE (μ.map H₁) (ν.map H₂) δ e`, the reconstruction `Φ` is `1`-Lipschitz for the
extended distance `d`, `P₁` is within `a` of `Φ ∘ H₁` on `G₁` and `P₂` is within `a'` of `Φ ∘ H₂` on
`G₂`, then for every set `A`,
`μ (P₁ ⁻¹' A) ≤ ν {ω | ∃ f ∈ A, d (P₂ ω) f < a' + δ + a} + e + μ G₁ᶜ + ν G₂ᶜ`. -/
theorem measure_preimage_le_of_prokhorovLE_of_approx {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {μ : Measure Ω₁} {ν : Measure Ω₂} {d : Y → Y → ℝ≥0∞}
    (hd : ∀ x y z, d x z ≤ d x y + d y z) {Φ : E → Y} (hΦ : ∀ x x', d (Φ x) (Φ x') ≤ edist x x')
    {H₁ : Ω₁ → E} {H₂ : Ω₂ → E} (hH₁ : Measurable H₁) (hH₂ : Measurable H₂) {δ e a a' : ℝ}
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (hδ : 0 ≤ δ) (hP : ProkhorovLE (μ.map H₁) (ν.map H₂) δ e)
    {P₁ : Ω₁ → Y} {P₂ : Ω₂ → Y} {G₁ : Set Ω₁} {G₂ : Set Ω₂}
    (hG₁ : ∀ ω ∈ G₁, d (Φ (H₁ ω)) (P₁ ω) < ENNReal.ofReal a)
    (hG₂ : ∀ ω ∈ G₂, d (P₂ ω) (Φ (H₂ ω)) < ENNReal.ofReal a') (A : Set Y) :
    μ (P₁ ⁻¹' A) ≤ ν {ω | ∃ f ∈ A, d (P₂ ω) f < ENNReal.ofReal (a' + δ + a)} +
      ENNReal.ofReal e + μ G₁ᶜ + ν G₂ᶜ := by
  set U : Set E := {x | ∃ f ∈ A, d (Φ x) f < ENNReal.ofReal a}
  have hU : MeasurableSet U :=
    (isOpen_setOf_exists_lt_of_lipschitz hd hΦ A (ENNReal.ofReal a)).measurableSet
  have hT : MeasurableSet (thickening δ U) := isOpen_thickening.measurableSet
  set V : Set Ω₂ := {ω | ∃ f ∈ A, d (P₂ ω) f < ENNReal.ofReal (a' + δ + a)}
  -- the curves of `P₁` in `A` have skeletons in `U`, off `G₁ᶜ`
  have h1 : P₁ ⁻¹' A ⊆ H₁ ⁻¹' U ∪ G₁ᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G₁
    · exact Or.inl ⟨P₁ ω, hω, hG₁ ω hg⟩
    · exact Or.inr hg
  -- skeletons of `P₂` in the `δ`-thickening of `U` give curves within `a' + δ + a` of `A`, off `G₂ᶜ`
  have h2 : H₂ ⁻¹' thickening δ U ⊆ V ∪ G₂ᶜ := by
    intro ω hω
    by_cases hg : ω ∈ G₂
    · left
      obtain ⟨x', ⟨f, hfA, hx'f⟩, hdist⟩ := (mem_thickening_iff_exists_edist_lt U (H₂ ω)).mp hω
      refine ⟨f, hfA, ?_⟩
      calc d (P₂ ω) f ≤ d (P₂ ω) (Φ (H₂ ω)) + d (Φ (H₂ ω)) f := hd _ _ _
        _ ≤ d (P₂ ω) (Φ (H₂ ω)) + (d (Φ (H₂ ω)) (Φ x') + d (Φ x') f) := by gcongr; exact hd _ _ _
        _ < ENNReal.ofReal a' + (ENNReal.ofReal δ + ENNReal.ofReal a) := by
          refine ENNReal.add_lt_add (hG₂ ω hg) (ENNReal.add_lt_add_of_le_of_lt ?_ ?_ hx'f)
          · exact ne_top_of_lt ((hΦ _ _).trans_lt hdist)
          · exact (hΦ _ _).trans hdist.le
        _ = ENNReal.ofReal (a' + δ + a) := by
          rw [← add_assoc, ENNReal.ofReal_add (add_nonneg ha' hδ) ha, ENNReal.ofReal_add ha' hδ]
    · exact Or.inr hg
  calc μ (P₁ ⁻¹' A) ≤ μ (H₁ ⁻¹' U ∪ G₁ᶜ) := measure_mono h1
    _ ≤ μ (H₁ ⁻¹' U) + μ G₁ᶜ := measure_union_le _ _
    _ = μ.map H₁ U + μ G₁ᶜ := by rw [Measure.map_apply hH₁ hU]
    _ ≤ (ν.map H₂ (thickening δ U) + ENNReal.ofReal e) + μ G₁ᶜ := by gcongr; exact hP U hU
    _ = (ν (H₂ ⁻¹' thickening δ U) + ENNReal.ofReal e) + μ G₁ᶜ := by
          rw [Measure.map_apply hH₂ hT]
    _ ≤ ((ν V + ν G₂ᶜ) + ENNReal.ofReal e) + μ G₁ᶜ := by
          gcongr; exact (measure_mono h2).trans (measure_union_le _ _)
    _ = ν V + ENNReal.ofReal e + μ G₁ᶜ + ν G₂ᶜ := by ring

end LatticeProb

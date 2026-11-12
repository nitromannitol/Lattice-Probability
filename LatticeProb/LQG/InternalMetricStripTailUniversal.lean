import Mathlib
import LatticeProb.LQG.InternalMetricSetDistMeasurable

/-!
# Strip tails of the internal metric are realization-free

The four strip configurations around the halves of the unit square (`horizontalCrossingDist`, `verticalCrossingDist`) are
internal distances between compact segments in an open strip. By `IsLQGMetric.measure_internalSetDist_ge_eq` the
probability that such a strip distance of `D_h` is at least `L` is the same for every whole-plane GFF `h`, on whichever
probability space it is realized. Hence an upper bound for the strip tails of one realization of the whole-plane GFF gives,
by the union bound over the four strips, an upper bound for the probability that the unit square has no hard
half-crossings of length at most `L`, uniformly over all realizations
(`IsLQGMetric.measure_not_hasShortHalfCrossings_le_of_realization`).
-/

namespace LatticeProb.LQG

open Set MeasureTheory
open scoped ENNReal
open LatticeProb.Gauss

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω Ω' : Type} [MeasurableSpace Ω]
  [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}

/-- The probability that the horizontal strip distance at height `y₀` is at least `L` is the same in all realizations of
the whole-plane GFF. -/
theorem IsLQGMetric.measure_horizontalCrossingDist_ge_eq (h𝔇 : IsLQGMetric γ ξ 𝔇) (y₀ : ℝ) (L : ℝ≥0∞)
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc') :
    P {ω | L ≤ horizontalCrossingDist (𝔇 (hC ω)) y₀} =
      Q {ω | L ≤ horizontalCrossingDist (𝔇 (hC' ω)) y₀} := by
  have hsub : ∀ x : ℝ, x ∈ ({-1 / 2, 3 / 2} : Set ℝ) → x ∈ Ioo (-1 : ℝ) 2 := by
    intro x hx
    rcases hx with rfl | rfl
    · constructor <;> norm_num
    · constructor <;> norm_num
  have hI : Icc (y₀ + 1 / 8) (y₀ + 3 / 8) ⊆ Ioo y₀ (y₀ + 1 / 2) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact h𝔇.measure_internalSetDist_ge_eq (isOpen_Ioo.reProdIm isOpen_Ioo)
    (isCompact_singleton.reProdIm isCompact_Icc) (isCompact_singleton.reProdIm isCompact_Icc)
    (fun z hz => ⟨hsub _ (Or.inl hz.1), hI hz.2⟩) (fun z hz => ⟨hsub _ (Or.inr hz.1), hI hz.2⟩) L hP hQ

/-- The probability that the vertical strip distance at abscissa `x₀` is at least `L` is the same in all realizations of
the whole-plane GFF. -/
theorem IsLQGMetric.measure_verticalCrossingDist_ge_eq (h𝔇 : IsLQGMetric γ ξ 𝔇) (x₀ : ℝ) (L : ℝ≥0∞)
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc') :
    P {ω | L ≤ verticalCrossingDist (𝔇 (hC ω)) x₀} =
      Q {ω | L ≤ verticalCrossingDist (𝔇 (hC' ω)) x₀} := by
  have hsub : ∀ x : ℝ, x ∈ ({3 / 2, -1 / 2} : Set ℝ) → x ∈ Ioo (-1 : ℝ) 2 := by
    intro x hx
    rcases hx with rfl | rfl
    · constructor <;> norm_num
    · constructor <;> norm_num
  have hI : Icc (x₀ + 1 / 8) (x₀ + 3 / 8) ⊆ Ioo x₀ (x₀ + 1 / 2) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact h𝔇.measure_internalSetDist_ge_eq (isOpen_Ioo.reProdIm isOpen_Ioo)
    (isCompact_Icc.reProdIm isCompact_singleton) (isCompact_Icc.reProdIm isCompact_singleton)
    (fun z hz => ⟨hI hz.1, hsub _ (Or.inl hz.2)⟩) (fun z hz => ⟨hI hz.1, hsub _ (Or.inr hz.2)⟩) L hP hQ

/-- **The crossing tail of the unit square follows from the strip tails of one realization.** Let `𝔇` be a γ-LQG metric and
`(Ω', Q, hC', hcirc')` one realization of the whole-plane GFF in which each of the four strip distances of `D_{h'}` is at
least `L` with probability at most `q`. Then in every realization `(Ω, P, hC, hcirc)` the probability that `[0, 1]²`
has no hard half-crossings of `D_h`-length at most `L` is at most `4 q`. -/
theorem IsLQGMetric.measure_not_hasShortHalfCrossings_le_of_realization (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc') (L q : ℝ≥0∞)
    (hh : ∀ y₀ ∈ ({0, 1 / 2} : Set ℝ), Q {ω | L ≤ horizontalCrossingDist (𝔇 (hC' ω)) y₀} ≤ q)
    (hv : ∀ x₀ ∈ ({0, 1 / 2} : Set ℝ), Q {ω | L ≤ verticalCrossingDist (𝔇 (hC' ω)) x₀} ≤ q) :
    P {ω | ¬ HasShortHalfCrossings (𝔇 (hC ω)) 0 1 0 1 L} ≤ 4 * q :=
  measure_not_hasShortHalfCrossings_zero_one_le_four_mul P (fun ω => 𝔇 (hC ω)) L q
    (fun y₀ hy₀ => (h𝔇.measure_horizontalCrossingDist_ge_eq y₀ L hP hQ).trans_le (hh y₀ hy₀))
    (fun x₀ hx₀ => (h𝔇.measure_verticalCrossingDist_ge_eq x₀ L hP hQ).trans_le (hv x₀ hx₀))

/-- **Uniform crossing tail from one realization.** Let `𝔇` be a γ-LQG metric and `(Ω', Q, hC', hcirc')` one realization
of the whole-plane GFF in which, for each `n`, the strip distances of `D_{h'}` are at least `e^{δ n}` with probability
at most `q n`. Then in every realization of the whole-plane GFF on a probability space in `Type`, the probability that the
unit square has no hard half-crossings of `D_h`-length at most `e^{δ n}` is at most `4 q n`. -/
theorem IsLQGMetric.uniform_tail_of_realization (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hQ : IsWholePlaneGFF Q hC' hcirc') (δ : ℝ) (q : ℕ → ℝ≥0∞)
    (hh : ∀ n : ℕ, ∀ y₀ ∈ ({0, 1 / 2} : Set ℝ),
      Q {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ horizontalCrossingDist (𝔇 (hC' ω)) y₀} ≤ q n)
    (hv : ∀ n : ℕ, ∀ x₀ ∈ ({0, 1 / 2} : Set ℝ),
      Q {ω | ENNReal.ofReal (Real.exp (δ * n)) ≤ verticalCrossingDist (𝔇 (hC' ω)) x₀} ≤ q n) :
    ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) (hC₁ : Ω₁ → (ℂ → ℝ) → ℝ)
      (hcirc₁ : Ω₁ → ℝ → ℂ → ℝ), IsWholePlaneGFF P₁ hC₁ hcirc₁ → ∀ n : ℕ,
        P₁ {ω | ¬ HasShortHalfCrossings (𝔇 (hC₁ ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤
          4 * q n :=
  fun _ _ _ _ _ hG n => h𝔇.measure_not_hasShortHalfCrossings_le_of_realization hG hQ _ _ (hh n) (hv n)

end LatticeProb.LQG

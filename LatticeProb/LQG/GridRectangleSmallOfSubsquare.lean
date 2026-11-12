import LatticeProb.LQG.ClosedDyadicGridRectangleSmall

/-!
# From small closed dyadic subsquares to small grid rectangles

Let `S = [a, a + s] × [b, b + s]` and let `E` be a random function on `ℂ × ℂ` whose real part `ofReal ∘ E` satisfies
the triangle inequality almost surely (for instance a Weyl scaling of a length metric). If for every threshold
`ε' > 0` the (outer) probability that some closed dyadic subsquare of `S` of level `m` has `E`-internal diameter larger
than `ε'` tends to `0` as `m → ∞`, then the same holds for the closed grid rectangles of level `m` made of at most
`(M + 1) × (M + 1)` subsquares, for each fixed `M`. The internal diameter of such a rectangle is at most the sum of the
internal diameters of its subsquares (`internalMetric_closedDyadicSubsquare_grid_le`), so the threshold
`ε / (M + 1)²` for the subsquares gives the threshold `ε` for the rectangles.

## Main statements

* `LatticeProb.LQG.tendsto_measure_not_forall_internalMetric_gridRectangle_le_of_closedDyadicSubsquare`
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LatticeProb.LQG

/-- **Small grid rectangles from small closed dyadic subsquares.** Let `E` be a random function on `ℂ × ℂ` such that
almost surely `ofReal ∘ E` satisfies the triangle inequality, and let `S = [a, a + s] × [b, b + s]` with `s ≥ 0`.
Suppose that for every `ε' > 0` the (outer) probability that some closed dyadic subsquare `S_{m,i,j}` of `S` contains
two points at `E`-internal distance in `S_{m,i,j}` larger than `ε'` tends to `0` as `m → ∞`. Then for every `M : ℕ`
and `ε > 0`, the (outer) probability that some closed rectangle
`[a + i₀ h, a + (i₀ + K + 1) h] × [b + j₀ h, b + (j₀ + L + 1) h]` (`h = 2⁻ᵐ s`, `K, L ≤ M`) of the level-`m` grid of
`S` contains two points at `E`-internal distance in the rectangle larger than `ε` tends to `0` as `m → ∞`. -/
theorem tendsto_measure_not_forall_internalMetric_gridRectangle_le_of_closedDyadicSubsquare {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {E : Ω → ℂ → ℂ → ℝ}
    (htri : ∀ᵐ ω ∂P, ∀ x y z,
      ENNReal.ofReal (E ω x z) ≤ ENNReal.ofReal (E ω x y) + ENNReal.ofReal (E ω y z))
    {a b s : ℝ} (hs : 0 ≤ s)
    (hsub : ∀ ε' : ℝ, 0 < ε' → Tendsto (fun m : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ m → j < 2 ^ m →
      ∀ z ∈ closedDyadicSubsquare a b s m i j, ∀ w ∈ closedDyadicSubsquare a b s m i j,
        internalMetric (E ω) (closedDyadicSubsquare a b s m i j) z w ≤ ENNReal.ofReal ε'}) atTop (𝓝 0))
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => P {ω | ¬ ∀ i₀ j₀ K L : ℕ, K ≤ M → L ≤ M → i₀ + K < 2 ^ m → j₀ + L < 2 ^ m →
      ∀ u ∈ Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
          Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m)),
        ∀ v ∈ Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
          Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m)),
        internalMetric (E ω) (Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
          Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m))) u v ≤ ENNReal.ofReal ε})
      atTop (𝓝 0) := by
  have hε' : 0 < ε / (((M : ℝ) + 1) * ((M : ℝ) + 1)) := div_pos hε (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hsub _ hε') (fun _ => zero_le) fun m => ?_
  refine measure_mono_ae ?_
  filter_upwards [htri] with ω htriω hω
  intro hgood
  refine hω fun i₀ j₀ K L hK hL hiK hjL u hu v hv => ?_
  refine (internalMetric_closedDyadicSubsquare_grid_le htriω hs
    (A := ENNReal.ofReal (ε / (((M : ℝ) + 1) * ((M : ℝ) + 1))))
    (fun k hk l hl => hgood (i₀ + k) (j₀ + l) (lt_of_le_of_lt (Nat.add_le_add_left hk i₀) hiK)
      (lt_of_le_of_lt (Nat.add_le_add_left hl j₀) hjL)) u hu v hv).trans ?_
  calc ((K : ℝ≥0∞) + 1) * ((L : ℝ≥0∞) + 1) * ENNReal.ofReal (ε / (((M : ℝ) + 1) * ((M : ℝ) + 1)))
      ≤ ((M : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1) * ENNReal.ofReal (ε / (((M : ℝ) + 1) * ((M : ℝ) + 1))) := by
        gcongr
    _ = ENNReal.ofReal ε := natCast_add_one_mul_natCast_add_one_mul_ofReal_div M ε

end LatticeProb.LQG

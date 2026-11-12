import LatticeProb.LQG.InternalMetricDyadicSmallWeyl
import LatticeProb.LQG.ClosedDyadicSubsquareUnion

/-!
# Uniformly small internal diameters of grid rectangles of closed dyadic subsquares

Let `S = [a, a + s] × [b, b + s]` with `s > 0`, `𝔇` a γ-LQG metric, `h` a whole-plane GFF and `E = e^{ξ f} · D_h`
almost surely a Weyl scaling of `D_h` (Gwynne-Miller, arXiv:1905.00383, (1.8)) by a deterministic weight `f`
continuous on `S`. Under the uniform unit-square crossing tail, the probability that some closed dyadic subsquare of
`S` of level `m` has `E`-internal diameter larger than a fixed threshold tends to `0`
(`IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn`).

A closed rectangle on the level-`m` grid of `S` made of `(K + 1) × (L + 1)` subsquares has `E`-internal diameter at
most `(K + 1)(L + 1)` times the largest internal diameter of its subsquares (`internalMetric_closedDyadicSubsquare_grid_le`;
`E` has the triangle inequality, being a Weyl scaling of a length metric). Hence for every fixed `M`, the probability
that some grid rectangle of at most `(M + 1) × (M + 1)` level-`m` subsquares has `E`-internal diameter larger than `ε`
tends to `0`: apply the subsquare statement with the threshold `ε / (M + 1)²`.

## Main statements

* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_gridRectangle_le_of_continuousOn`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `(M + 1)² · (ε / (M + 1)²) = ε` in `ℝ≥0∞`. -/
theorem natCast_add_one_mul_natCast_add_one_mul_ofReal_div (M : ℕ) (ε : ℝ) :
    ((M : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1) * ENNReal.ofReal (ε / (((M : ℝ) + 1) * ((M : ℝ) + 1))) =
      ENNReal.ofReal ε := by
  have h1 : ((M : ℝ≥0∞) + 1) = ENNReal.ofReal ((M : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg M) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have h0 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have hM : (0 : ℝ) < ((M : ℝ) + 1) * ((M : ℝ) + 1) := by positivity
  rw [h1, ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul hM.le]
  congr 1
  field_simp

/-- **Uniformly small internal diameters of grid rectangles of closed dyadic subsquares for a Weyl-scaled LQG
metric.** Let `𝔇` be a γ-LQG metric with `ξ > 0`, `h` a whole-plane GFF, `S = [a, a + s] × [b, b + s]` with `s > 0`
and `δ < θ < ξ (Q - 2) log 2`, and assume the uniform unit-square crossing tail `huniv` with `∑ₙ 4ⁿ p n < ∞`. Let `E`
be a random function which is almost surely the Weyl scaling `e^{ξ f} · D_h` of `D_h` by a deterministic weight `f`
continuous on `S`, and let `M : ℕ`. Then for every `ε > 0`, the (outer) probability that some closed rectangle
`[a + i₀ h, a + (i₀ + K + 1) h] × [b + j₀ h, b + (j₀ + L + 1) h]` (`h = 2⁻ᵐ s`, `K, L ≤ M`) on the level-`m` grid of
`S` contains two points at `E`-internal distance in the rectangle larger than `ε` tends to `0` as `m → ∞`. -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_gridRectangle_le_of_continuousOn
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ)
    {θ δ : ℝ} (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {E : Ω → ℂ → ℂ → ℝ} {f : ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ f x y)
    (hf : ContinuousOn f (Icc a (a + s) ×ℂ Icc b (b + s))) (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m : ℕ => P {ω | ¬ ∀ i₀ j₀ K L : ℕ, K ≤ M → L ≤ M → i₀ + K < 2 ^ m → j₀ + L < 2 ^ m →
      ∀ u ∈ Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
          Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m)),
        ∀ v ∈ Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
          Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m)),
        internalMetric (E ω) (Icc (a + (i₀ : ℝ) * (s / 2 ^ m)) (a + ((i₀ : ℝ) + K + 1) * (s / 2 ^ m)) ×ℂ
          Icc (b + (j₀ : ℝ) * (s / 2 ^ m)) (b + ((j₀ : ℝ) + L + 1) * (s / 2 ^ m))) u v ≤ ENNReal.ofReal ε})
      atTop (𝓝 0) := by
  have hε' : 0 < ε / (((M : ℝ) + 1) * ((M : ℝ) + 1)) := div_pos hε (by positivity)
  have hmain :=
    h𝔇.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn hG hs hξ hθ
      hδ huniv hp hE hf hε'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmain (fun _ => zero_le) fun m => ?_
  refine measure_mono_ae ?_
  filter_upwards [(h𝔇.ae_isEuclideanLengthMetric_self hG).and hE] with ω hωE hω
  obtain ⟨hD, hEω⟩ := hωE
  intro hgood
  refine hω fun i₀ j₀ K L hK hL hiK hjL u hu v hv => ?_
  have htri : ∀ x y z, ENNReal.ofReal (E ω x z) ≤ ENNReal.ofReal (E ω x y) + ENNReal.ofReal (E ω y z) := by
    intro x y z
    rw [hEω, hEω, hEω]
    exact hD.weylScaling_triangle ξ f x y z
  refine (internalMetric_closedDyadicSubsquare_grid_le htri hs.le
    (A := ENNReal.ofReal (ε / (((M : ℝ) + 1) * ((M : ℝ) + 1))))
    (fun k hk l hl => hgood (i₀ + k) (j₀ + l) (lt_of_le_of_lt (Nat.add_le_add_left hk i₀) hiK)
      (lt_of_le_of_lt (Nat.add_le_add_left hl j₀) hjL)) u hu v hv).trans ?_
  calc ((K : ℝ≥0∞) + 1) * ((L : ℝ≥0∞) + 1) * ENNReal.ofReal (ε / (((M : ℝ) + 1) * ((M : ℝ) + 1)))
      ≤ ((M : ℝ≥0∞) + 1) * ((M : ℝ≥0∞) + 1) * ENNReal.ofReal (ε / (((M : ℝ) + 1) * ((M : ℝ) + 1))) := by
        gcongr
    _ = ENNReal.ofReal ε := natCast_add_one_mul_natCast_add_one_mul_ofReal_div M ε

end LatticeProb.LQG

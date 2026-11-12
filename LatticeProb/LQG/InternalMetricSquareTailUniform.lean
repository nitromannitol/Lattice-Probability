import LatticeProb.LQG.InternalMetricSquareTailExp
import LatticeProb.LQG.HalfCrossingScaling
import LatticeProb.Prob.DyadicSumBound

/-!
# Finite internal diameter of a closed square from a uniform unit-square crossing tail

Let `𝔇` be a γ-LQG metric and `h` a whole-plane GFF normalized by its circle average, and consider the closed square
`S = [a, a + s] × [b, b + s]`. Suppose that the probability that the unit square `[0, 1]²` has no half crossings of
`D_{h'}`-length at most `e^{δ n}` is at most `p n` for **every** whole-plane GFF `h'` on the same probability space, with
`∑ₙ 4ⁿ p n < ∞`. This is the form in which the crossing estimate of Dubédat-Falconet-Gwynne-Pfeffer-Sun
(arXiv:1905.00380, Proposition 3.1) enters the proof of their Proposition 3.10. Then:

* every closed dyadic subsquare of `S` almost surely has half crossings of finite `D_h`-length, since its half crossings
  are the images of those of the unit square for the recentred field `h(r · + z) - h_r(z)`, which is again a whole-plane
  GFF, scaled by the finite factor `e^{ξ (h_r(z) + Q log r)}`, and `p n → 0`;
* the unit-square tails of the recentred fields of all dyadic subsquares are summable, since each is at most `p n` and
  there are `4ⁿ` subsquares at level `n`;
* hence, when `ξ > 0` and `δ < θ < ξ (Q - 2) log 2`, the internal diameter of `S` is almost surely finite.

## Main statements

* `LatticeProb.LQG.IsLQGMetric.ae_exists_hasShortHalfCrossings_of_tendsto`
* `LatticeProb.LQG.IsLQGMetric.ae_exists_hasShortHalfCrossings_dyadic_of_tendsto`
* `LatticeProb.LQG.tsum_unitTail_recentredPairing_ne_top`
* `LatticeProb.LQG.IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_uniformUnitTail`
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Finite half crossings from a vanishing tail at scale `r` around `z`.** For a γ-LQG metric `𝔇`, a whole-plane GFF
`h`, `r > 0` and `z ∈ ℂ`, let `[X₀, X₁] × [Y₀, Y₁]` be the image of `[x₀, x₁] × [y₀, y₁]` under `x ↦ r x + z`. If, for
finite thresholds `A m`, the probability that `[x₀, x₁] × [y₀, y₁]` has no half crossings of length at most `A m` for the
metric of `h' = h(r · + z) - h_r(z)` tends to `0`, then almost surely `[X₀, X₁] × [Y₀, Y₁]` has half crossings of finite
`D_h`-length. -/
theorem IsLQGMetric.ae_exists_hasShortHalfCrossings_of_tendsto (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) {x₀ x₁ y₀ y₁ X₀ X₁ Y₀ Y₁ : ℝ}
    (hX₀ : X₀ = r * x₀ + z.re) (hX₁ : X₁ = r * x₁ + z.re) (hY₀ : Y₀ = r * y₀ + z.im)
    (hY₁ : Y₁ = r * y₁ + z.im) (A : ℕ → ℝ≥0∞) (hA : ∀ m, A m ≠ ⊤)
    (htail : Tendsto (fun m => P {ω | ¬ HasShortHalfCrossings (𝔇 (recentredPairing hC hcirc r z ω))
      x₀ x₁ y₀ y₁ (A m)}) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ HasShortHalfCrossings (𝔇 (hC ω)) X₀ X₁ Y₀ Y₁ L := by
  subst hX₀ hX₁ hY₀ hY₁
  rw [ae_iff]
  refine le_antisymm (ge_of_tendsto' htail fun m => measure_mono_ae ?_) zero_le
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ¬ ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ HasShortHalfCrossings (𝔇 (hC ω)) (r * x₀ + z.re)
      (r * x₁ + z.re) (r * y₀ + z.im) (r * y₁ + z.im) L} →
      ω ∈ {ω | ¬ HasShortHalfCrossings (𝔇 (recentredPairing hC hcirc r z ω)) x₀ x₁ y₀ y₁ (A m)} := by
    filter_upwards [h𝔇.ae_hasShortHalfCrossings_scaling hG hr z] with ω hω hbad
    intro hm
    exact hbad ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hA m), hω x₀ x₁ y₀ y₁ (A m) hm⟩
  exact hsub

/-- **Finite half crossings of a closed dyadic subsquare.** For a γ-LQG metric `𝔇`, a whole-plane GFF `h`, a square
`[a, a + s] × [b, b + s]` with `s > 0` and its closed dyadic subsquare of level `n` and index `(i, j)`, of side
`r = s / 2ⁿ` and bottom-left corner `z = (a + i r, b + j r)`: if, for finite thresholds `A m`, the probability that the
unit square has no half crossings of length at most `A m` for the metric of `h(r · + z) - h_r(z)` tends to `0`, then
almost surely the subsquare has half crossings of finite `D_h`-length. -/
theorem IsLQGMetric.ae_exists_hasShortHalfCrossings_dyadic_of_tendsto (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (A : ℕ → ℝ≥0∞) (hA : ∀ m, A m ≠ ⊤)
    (n i j : ℕ)
    (htail : Tendsto (fun m => P {ω | ¬ HasShortHalfCrossings
      (𝔇 (recentredPairing hC hcirc (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ ω)) 0 1 0 1 (A m)})
      atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ HasShortHalfCrossings (𝔇 (hC ω)) (a + i * (s / 2 ^ n))
      (a + (i + 1) * (s / 2 ^ n)) (b + j * (s / 2 ^ n)) (b + (j + 1) * (s / 2 ^ n)) L :=
  h𝔇.ae_exists_hasShortHalfCrossings_of_tendsto hG (by positivity) _
    (show _ = s / 2 ^ n * 0 + (a + i * (s / 2 ^ n)) by ring)
    (show _ = s / 2 ^ n * 1 + (a + i * (s / 2 ^ n)) by ring)
    (show _ = s / 2 ^ n * 0 + (b + j * (s / 2 ^ n)) by ring)
    (show _ = s / 2 ^ n * 1 + (b + j * (s / 2 ^ n)) by ring) A hA htail

/-- **Summable unit-square tails over the dyadic subsquares.** Let `h` be a whole-plane GFF and `S` the square
`[a, a + s] × [b, b + s]` with `s > 0`. If for every whole-plane GFF `h'` on the same probability space the
probability that the unit square has no half crossings of `D_{h'}`-length at most `A n` is at most `p n`, and
`∑ₙ 4ⁿ p n < ∞`, then the unit-square tails of the recentred fields `h(r_n · + z_{n,i,j}) - h_{r_n}(z_{n,i,j})` of the
closed dyadic subsquares of `S` are summable over all levels. -/
theorem tsum_unitTail_recentredPairing_ne_top (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s)
    (A p : ℕ → ℝ≥0∞)
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (A n)} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∑' n : ℕ, ∑ i ∈ Finset.range (2 ^ n), ∑ j ∈ Finset.range (2 ^ n),
      P {ω | ¬ HasShortHalfCrossings
        (𝔇 (recentredPairing hC hcirc (s / 2 ^ n) ⟨a + i * (s / 2 ^ n), b + j * (s / 2 ^ n)⟩ ω)) 0 1 0 1
          (A n)} ≠ ⊤ :=
  tsum_tsum_sum_le_of_le_four_pow (fun n i j _ _ =>
    huniv _ _ (isWholePlaneGFF_recentredPairing hG (by positivity) _) n) hp

/-- If `∑ₙ 4ⁿ p n < ∞` in `ℝ≥0∞` then `p n → 0`. -/
theorem tendsto_zero_of_tsum_four_pow_mul_ne_top {p : ℕ → ℝ≥0∞} (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    Tendsto p atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top <| ne_top_of_le_ne_top hp <| ENNReal.tsum_le_tsum fun n =>
    le_mul_of_one_le_left zero_le (one_le_pow₀ (by norm_num))

/-- **Finite internal diameter of a closed square from a uniform unit-square crossing tail**
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, proof of Proposition 3.10, with their Proposition 3.1 as the
hypothesis `huniv`). Let `𝔇` be a γ-LQG metric with `ξ > 0`, `h` a whole-plane GFF and `S = [a, a + s] × [b, b + s]`
with `s > 0`. Let `δ < θ < ξ (Q - 2) log 2`. Suppose that for every whole-plane GFF `h'` on the same probability space
and every `n`, the probability that the unit square `[0, 1]²` has no half crossings of `D_{h'}`-length at most `e^{δ n}`
is at most `p n`, where `∑ₙ 4ⁿ p n < ∞`. Then almost surely there is a real `A` with `D_h(z, w; S) ≤ A` for all
`z, w ∈ S`. -/
theorem IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_uniformUnitTail (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ w ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric (𝔇 (hC ω)) (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ ENNReal.ofReal A := by
  refine h𝔇.ae_exists_internalMetric_closedSquare_le_of_unitTail hG hs hξ hθ hδ (fun n i j _ _ => ?_)
    (tsum_unitTail_recentredPairing_ne_top hG hs _ p huniv hp)
  refine h𝔇.ae_exists_hasShortHalfCrossings_dyadic_of_tendsto hG hs
    (fun m => ENNReal.ofReal (Real.exp (δ * m))) (fun _ => ENNReal.ofReal_ne_top) n i j ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_zero_of_tsum_four_pow_mul_ne_top hp) (fun _ => zero_le)
    (huniv _ _ (isWholePlaneGFF_recentredPairing hG (by positivity) _))

end LatticeProb.LQG

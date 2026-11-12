import LatticeProb.LQG.InternalMetricSquareTailUniform
import LatticeProb.LQG.WeylChainBound

/-!
# Finite internal diameter of a closed square for a Weyl-scaled γ-LQG metric

Let `𝔇` be a γ-LQG metric, `h` a whole-plane GFF and `S = [a, a + s] × [b, b + s]`. Under the uniform unit-square
crossing tail of `IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_uniformUnitTail`, the internal diameter of `S`
for `D_h` is almost surely finite. If `E = e^{ξ f} · D_h` is a Weyl scaling of `D_h` (Gwynne-Miller, arXiv:1905.00383,
(1.8)) by a weight with `ξ f ≤ B` on `S`, then `E(z, w; S) ≤ e^B D_h(z, w; S)` (`internalMetric_le_of_weylScaling`), so
the internal diameter of `S` for `E` is almost surely finite as well. This applies to the metric
`D_{h - α log |·|} = |·|^{-α ξ} · D_h` of a whole-plane GFF plus a logarithmic singularity at `0`
(Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, p. 9) on every closed square not containing `0`, where the
weight `-α log |·|` is continuous.

## Main statements

* `LatticeProb.LQG.IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_weylScaling`
* `LatticeProb.LQG.IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_weylScaling_continuousOn`
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Finite internal diameter of a closed square for a Weyl-scaled γ-LQG metric.** Let `𝔇` be a γ-LQG metric with
`ξ > 0`, `h` a whole-plane GFF, `S = [a, a + s] × [b, b + s]` with `s > 0` and `δ < θ < ξ (Q - 2) log 2`. Suppose that
for every whole-plane GFF `h'` on the same probability space and every `n`, the probability that the unit square has no
half crossings of `D_{h'}`-length at most `e^{δ n}` is at most `p n`, where `∑ₙ 4ⁿ p n < ∞`. Let `E` be a random function
which is almost surely the Weyl scaling `e^{ξ f} · D_h` of `D_h` by a random weight `f` with `ξ f` almost surely bounded
above on `S`. Then almost surely there is a real `A` with `E(z, w; S) ≤ A` for all `z, w ∈ S`. -/
theorem IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_weylScaling (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {E : Ω → ℂ → ℂ → ℝ} {f : Ω → ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ (f ω) x y)
    (hf : ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ξ * f ω z ≤ B) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ w ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric (E ω) (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ ENNReal.ofReal A := by
  filter_upwards [h𝔇.ae_exists_internalMetric_closedSquare_le_of_uniformUnitTail hG hs hξ hθ hδ huniv hp,
    h𝔇.ae_isEuclideanLengthMetric_self hG, hE, hf] with ω hA hD hEω hB
  obtain ⟨A, hA⟩ := hA
  obtain ⟨B, hB⟩ := hB
  refine ⟨Real.exp B * A, fun z hz w hw => ?_⟩
  calc internalMetric (E ω) (Icc a (a + s) ×ℂ Icc b (b + s)) z w
      ≤ ENNReal.ofReal (Real.exp B) * internalMetric (𝔇 (hC ω)) (Icc a (a + s) ×ℂ Icc b (b + s)) z w :=
        internalMetric_le_of_weylScaling hD hEω hB z w
    _ ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal A := by gcongr; exact hA z hz w hw
    _ = ENNReal.ofReal (Real.exp B * A) := (ENNReal.ofReal_mul (Real.exp_pos B).le).symm

/-- **Finite internal diameter of a closed square for a Weyl scaling by a continuous weight.** As
`IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_weylScaling`, for a deterministic weight `f` continuous on the
closed square `S` (for instance `f = -α log |·|` when `0 ∉ S`): if `E` is almost surely the Weyl scaling `e^{ξ f} · D_h`,
then almost surely the internal diameter of `S` for `E` is finite. -/
theorem IsLQGMetric.ae_exists_internalMetric_closedSquare_le_of_weylScaling_continuousOn
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ) {θ δ : ℝ}
    (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {E : Ω → ℂ → ℂ → ℝ} {f : ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ f x y)
    (hf : ContinuousOn f (Icc a (a + s) ×ℂ Icc b (b + s))) :
    ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ∀ w ∈ Icc a (a + s) ×ℂ Icc b (b + s),
      internalMetric (E ω) (Icc a (a + s) ×ℂ Icc b (b + s)) z w ≤ ENNReal.ofReal A := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.reProdIm isCompact_Icc).bddAbove_image (continuousOn_const.mul hf)
  exact h𝔇.ae_exists_internalMetric_closedSquare_le_of_weylScaling hG hs hξ hθ hδ huniv hp (f := fun _ => f) hE
    (ae_of_all _ fun _ => ⟨B, fun z hz => hB ⟨z, hz, rfl⟩⟩)

end LatticeProb.LQG

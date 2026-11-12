import LatticeProb.LQG.InternalMetricDyadicSmall
import LatticeProb.LQG.WeylChainBound

/-!
# Uniformly small internal diameters of the closed dyadic subsquares for a Weyl-scaled LQG metric

Let `S = [a, a + s] × [b, b + s]` with `s > 0`, `𝔇` a γ-LQG metric and `h` a whole-plane GFF. Under the uniform
unit-square crossing tail, the probability that some closed dyadic subsquare of `S` of level `n` has `D_h`-internal
diameter larger than a fixed threshold tends to `0`
(`IsLQGMetric.tendsto_measure_not_forall_internalMetric_closedDyadicSubsquare_le`). If `E = e^{ξ f} · D_h` is a Weyl
scaling of `D_h` (Gwynne-Miller, arXiv:1905.00383, (1.8)) by a deterministic weight with `ξ f ≤ B` on `S`, then
`E(z, w; V) ≤ e^B D_h(z, w; V)` for every `V ⊆ S` (`internalMetric_le_of_weylScaling`), so the same holds for `E` with
the threshold `ε` replaced by `e^{-B} ε` for `D_h`. This applies to `D_{h - α log |·|} = |·|^{-α ξ} · D_h` when `0 ∉ S`.

## Main statements

* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le`:
  the weight is bounded above on `S`.
* `LatticeProb.LQG.IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn`:
  the weight is continuous on `S`.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Uniformly small internal diameters of the closed dyadic subsquares for a Weyl-scaled LQG metric.** Let `𝔇` be a
γ-LQG metric with `ξ > 0`, `h` a whole-plane GFF, `S = [a, a + s] × [b, b + s]` with `s > 0` and
`δ < θ < ξ (Q - 2) log 2`, and assume the uniform unit-square crossing tail `huniv` with `∑ₙ 4ⁿ p n < ∞`. Let `E` be a
random function which is almost surely the Weyl scaling `e^{ξ f} · D_h` of `D_h` by a deterministic weight `f` with
`ξ f ≤ B` on `S`. Then for every `ε > 0`, the (outer) probability that some closed dyadic subsquare `S_{n,i,j}` of level
`n` contains two points at `E`-internal distance in `S_{n,i,j}` larger than `ε` tends to `0` as `n → ∞`. -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ)
    {θ δ : ℝ} (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {E : Ω → ℂ → ℂ → ℝ} {f : ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ f x y)
    {B : ℝ} (hf : ∀ z ∈ Icc a (a + s) ×ℂ Icc b (b + s), ξ * f z ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ z ∈ closedDyadicSubsquare a b s n i j, ∀ w ∈ closedDyadicSubsquare a b s n i j,
        internalMetric (E ω) (closedDyadicSubsquare a b s n i j) z w ≤ ENNReal.ofReal ε})
      atTop (𝓝 0) := by
  have hε' : 0 < ε * Real.exp (-B) := mul_pos hε (Real.exp_pos _)
  have hmain :=
    h𝔇.tendsto_measure_not_forall_internalMetric_closedDyadicSubsquare_le (a := a) (b := b) hG hs hξ hθ hδ huniv hp
      hε'
  set N : Set Ω := {ω | ¬ (IsEuclideanLengthMetric (𝔇 (hC ω)) ∧
    ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ f x y)} with hN_def
  have hN0 : P N = 0 := by
    have h := (h𝔇.ae_isEuclideanLengthMetric_self hG).and hE
    rwa [ae_iff] at h
  have hexp : ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (ε * Real.exp (-B)) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos B).le, mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      mul_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmain (fun _ => zero_le) fun n => ?_
  have hsub : {ω | ¬ ∀ i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ z ∈ closedDyadicSubsquare a b s n i j, ∀ w ∈ closedDyadicSubsquare a b s n i j,
        internalMetric (E ω) (closedDyadicSubsquare a b s n i j) z w ≤ ENNReal.ofReal ε} ⊆
      N ∪ {ω | ¬ ∀ i j : ℕ, i < 2 ^ n → j < 2 ^ n →
        ∀ z ∈ closedDyadicSubsquare a b s n i j, ∀ w ∈ closedDyadicSubsquare a b s n i j,
          internalMetric (𝔇 (hC ω)) (closedDyadicSubsquare a b s n i j) z w ≤
            ENNReal.ofReal (ε * Real.exp (-B))} := by
    intro ω hω
    by_contra hcon
    simp only [hN_def, mem_union, not_or, Set.mem_ofPred_eq, not_not] at hω hcon
    obtain ⟨⟨hD, hEω⟩, hgood⟩ := hcon
    refine hω fun i j hi hj z hz w hw => ?_
    calc internalMetric (E ω) (closedDyadicSubsquare a b s n i j) z w
        ≤ ENNReal.ofReal (Real.exp B) * internalMetric (𝔇 (hC ω)) (closedDyadicSubsquare a b s n i j) z w :=
          internalMetric_le_of_weylScaling hD hEω
            (fun u hu => hf u (closedDyadicSubsquare_subset hs hi hj hu)) z w
      _ ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (ε * Real.exp (-B)) := by
          gcongr
          exact hgood i j hi hj z hz w hw
      _ = ENNReal.ofReal ε := hexp
  calc P _ ≤ P (N ∪ _) := measure_mono hsub
    _ ≤ P N + _ := measure_union_le _ _
    _ = _ := by rw [hN0, zero_add]

/-- **Uniformly small internal diameters of the closed dyadic subsquares for a Weyl scaling by a continuous weight.**
As `IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le`, for a deterministic
weight `f` continuous on the closed square `S` (for instance `f = -α log |·|` when `0 ∉ S`). -/
theorem IsLQGMetric.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le_of_continuousOn
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc) {a b s : ℝ} (hs : 0 < s) (hξ : 0 < ξ)
    {θ δ : ℝ} (hθ : θ < ξ * (lqgQ γ - 2) * Real.log 2) (hδ : δ < θ) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) {E : Ω → ℂ → ℂ → ℝ} {f : ℂ → ℝ}
    (hE : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (𝔇 (hC ω)) ξ f x y)
    (hf : ContinuousOn f (Icc a (a + s) ×ℂ Icc b (b + s))) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => P {ω | ¬ ∀ i j : ℕ, i < 2 ^ n → j < 2 ^ n →
      ∀ z ∈ closedDyadicSubsquare a b s n i j, ∀ w ∈ closedDyadicSubsquare a b s n i j,
        internalMetric (E ω) (closedDyadicSubsquare a b s n i j) z w ≤ ENNReal.ofReal ε})
      atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.reProdIm isCompact_Icc).bddAbove_image (continuousOn_const.mul hf)
  exact h𝔇.tendsto_measure_not_forall_internalMetric_weylScaling_closedDyadicSubsquare_le hG hs hξ hθ hδ huniv hp
    hE (B := B) (fun z hz => hB ⟨z, hz, rfl⟩) hε

end LatticeProb.LQG

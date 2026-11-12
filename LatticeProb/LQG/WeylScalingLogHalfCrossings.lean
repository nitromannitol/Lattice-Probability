import LatticeProb.LQG.ExpShellInternalDiamSummable
import LatticeProb.LQG.WeylScalingLogShellCriterion
import LatticeProb.LQG.WeylScalingLocalBound

/-!
# Axioms I and III for the LQG metric of a field with a log singularity, `α₀ < Q`

Let `𝔇` be a γ-LQG metric with `0 < γ < 2`, `h^ℂ` a whole-plane GFF and `α₀ < Q`. Consider the Weyl scaling
`D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Proposition 3.17).
Assume the input of the union bound of loc. cit., Proposition 3.10: for every whole-plane GFF `h'` and every `n`, the
probability that `[0, 1]²` has no half crossings of `D_{h'}`-length at most `e^{δ n}` is at most `p n`, where
`δ < ξ (Q - 2) log 2` and `∑ₙ 4ⁿ p n < ∞`. Then almost surely

* (Axiom I) `D_h` is finite and its real part is a Euclidean length metric;
* (Axiom III) for every continuous `f`, `e^{ξ (f - α₀ log |·|)} · D_{h^ℂ} = e^{ξ f} · D_h`.

For `ξ α₀ ≤ 0` the weight `|x|^{-ξ α₀}` is bounded near the origin and no input is needed. For `ξ α₀ ≥ 0` the shell
series `∑ₖ e^{ξ α₀ k} diam(Aₖ)` is almost surely finite, which is the hypothesis of the shell criterion.

* `LatticeProb.LQG.IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_halfCrossings`: Axiom I.
* `LatticeProb.LQG.IsLQGMetric.ae_weylScaling_log_add_of_halfCrossings`: Axiom III.
-/

open MeasureTheory Filter Set LatticeProb.Gauss
open scoped ENNReal Topology

namespace LatticeProb.LQG

variable {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Axiom I for the LQG metric of a field with a log singularity, `α₀ < Q`.** Let `𝔇` be a γ-LQG metric,
`0 < γ < 2`, `h^ℂ` a whole-plane GFF, `α₀ < Q` and `δ < ξ (Q - 2) log 2`. Suppose that for every whole-plane GFF `h'`
and every `n` the probability that `[0, 1]²` has no half crossings of `D_{h'}`-length at most `e^{δ n}` is at most
`p n`, where `∑ₙ 4ⁿ p n < ∞`. Then almost surely `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` is finite and its real part is a
Euclidean length metric. -/
theorem IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_halfCrossings (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) {α₀ : ℝ} (hα : α₀ < lqgQ γ) {δ : ℝ}
    (hδ : δ < ξ * (lqgQ γ - 2) * Real.log 2) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v < ∞) ∧
      IsEuclideanLengthMetric fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
  rcases le_total 0 (ξ * α₀) with h0 | h0
  · exact h𝔇.ae_isEuclideanLengthMetric_weylScaling_log_of_summable hG h0
      (h𝔇.ae_tsum_expShell_internalDiam_ne_top_of_halfCrossings hG hγ hγ2 hα hδ huniv hp)
  · exact h𝔇.ae_isEuclideanLengthMetric_weylScaling_log_of_mul_nonpos hG h0

/-- **Axiom III for the LQG metric of a field with a log singularity, `α₀ < Q`.** Under the hypotheses of
`IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_halfCrossings`, almost surely, for every continuous `f`,
`e^{ξ (f - α₀ log |·|)} · D_{h^ℂ} = e^{ξ f} · D_h`, where `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}`. -/
theorem IsLQGMetric.ae_weylScaling_log_add_of_halfCrossings (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) {α₀ : ℝ} (hα : α₀ < lqgQ γ) {δ : ℝ}
    (hδ : δ < ξ * (lqgQ γ - 2) * Real.log 2) {p : ℕ → ℝ≥0∞}
    (huniv : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
      ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n)
    (hp : ∑' n, 4 ^ n * p n ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v,
      weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v =
        weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ f u v := by
  have hξ := h𝔇.xi_pos hγ hγ2
  rcases le_total 0 α₀ with h0 | h0
  · exact h𝔇.ae_weylScaling_log_add_of_summable hG hξ (mul_nonneg hξ.le h0)
      (h𝔇.ae_tsum_expShell_internalDiam_ne_top_of_halfCrossings hG hγ hγ2 hα hδ huniv hp)
  · exact h𝔇.ae_weylScaling_log_add_of_nonpos hG hξ h0

end LatticeProb.LQG

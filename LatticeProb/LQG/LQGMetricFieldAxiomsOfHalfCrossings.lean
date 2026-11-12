import LatticeProb.LQG.LQGMetric
import LatticeProb.LQG.WeylScalingLogHalfCrossings
import LatticeProb.LQG.WeylScalingLogLocality
import LatticeProb.LQG.WeylScalingHomeomorph

/-!
# The axioms I-IV for the LQG metric of a field with a log singularity, from short half crossings

Let `𝔇` be a γ-LQG metric with `0 < γ < 2`, `h^ℂ` a whole-plane GFF and `α₀ < Q`, and let
`D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` be the Weyl scaling by the logarithmic weight (Dubédat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380, Theorem 1.10 and Proposition 3.17). Assume the input of the union bound of loc. cit., Proposition 3.10:
there are `δ < ξ (Q - 2) log 2` and `p : ℕ → ℝ≥0∞` with `∑ₙ 4ⁿ p n < ∞` such that for every whole-plane GFF `h'` and
every `n` the probability that `[0, 1]²` has no half crossings of `D_{h'}`-length at most `e^{δ n}` is at most `p n`.
Then `D_h` satisfies the axioms I-IV of `LQGMetricFieldAxioms`:

* I (finiteness, Euclidean length metric): `IsLQGMetric.ae_isEuclideanLengthMetric_weylScaling_log_of_halfCrossings`;
* II (locality): `IsLQGMetric.exists_measurable_internalMetric_weylScaling_log`, with the almost sure finiteness of the
  weighted shell series `IsLQGMetric.ae_tsum_expShell_internalDiam_ne_top_of_halfCrossings`;
* III (Weyl scaling): `IsLQGMetric.ae_weylScaling_log_add_of_halfCrossings`;
* IV (coordinate change): `IsLQGMetric.ae_weylScaling_log_coordChange`, which needs no input.

* `LatticeProb.LQG.lqgMetricFieldAxioms_of_halfCrossings`: the assembly.
-/

open MeasureTheory LatticeProb.Gauss
open scoped ENNReal

namespace LatticeProb.LQG

/-- **The axioms I-IV for the LQG metric of `h^ℂ - α₀ log |·|`, from short half crossings.** Let `0 < γ < 2` and
suppose that for every γ-LQG metric `𝔇` with Weyl exponent `ξ` there are `δ < ξ (Q - 2) log 2` and
`p : ℕ → ℝ≥0∞` with `∑ₙ 4ⁿ p n < ∞` such that for every whole-plane GFF `h'` on `Ω` and every `n` the probability that
`[0, 1]²` has no half crossings of `D_{h'}`-length at most `e^{δ n}` is at most `p n`. Then `LQGMetricFieldAxioms`
holds: for every `α₀ < Q` the Weyl scaling `D_h = e^{-ξ α₀ log |·|} · D_{h^ℂ}` satisfies the axioms I-IV. -/
theorem lqgMetricFieldAxioms_of_halfCrossings {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ∃ (δ : ℝ) (p : ℕ → ℝ≥0∞), δ < ξ * (lqgQ γ - 2) * Real.log 2 ∧
        (∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC' hcirc' →
          ∀ n : ℕ, P {ω | ¬ HasShortHalfCrossings (𝔇 (hC' ω)) 0 1 0 1 (ENNReal.ofReal (Real.exp (δ * n)))} ≤ p n) ∧
        ∑' n, 4 ^ n * p n ≠ ⊤) :
    LQGMetricFieldAxioms P γ ξ α₀ hC hcirc := by
  intro hG hγ hγ2 hα 𝔇 h𝔇
  obtain ⟨δ, p, hδ, huniv, hp⟩ := h hγ hγ2 𝔇 h𝔇
  have hI := h𝔇.ae_isEuclideanLengthMetric_weylScaling_log_of_halfCrossings hG hγ hγ2 hα hδ huniv hp
  have hsum := h𝔇.ae_tsum_expShell_internalDiam_ne_top_of_halfCrossings hG hγ hγ2 hα hδ huniv hp
  exact ⟨hI, fun U hU => h𝔇.exists_measurable_internalMetric_weylScaling_log hG hγ hγ2 hsum hI hU,
    h𝔇.ae_weylScaling_log_add_of_halfCrossings hG hγ hγ2 hα hδ huniv hp,
    fun r hr z => h𝔇.ae_weylScaling_log_coordChange hG α₀ hr z⟩

end LatticeProb.LQG

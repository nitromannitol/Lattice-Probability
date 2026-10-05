/-
# The conditional-variance pairing for the Rosenthal cross term

`LatticeProb.crossTerm_le_variance_of_doob` (`Prob/BernsteinCrossTermBound.lean`) bounds the
cumulative cross term by `(p/(p-1))^{p-2} (∫ V^{p/2})^{2/p} (∫ |S n|^p)^{(p-2)/p}` **on the
hypothesis** of the `L^p` Doob maximal inequality `∫ (max |S|)^p ≤ (p/(p-1))^p ∫ |S n|^p`.
`LatticeProb.doob_maximal_crossTermMax` (`Prob/BernsteinDoobMaximal.lean`) supplies exactly that
hypothesis.  Composing them makes the pairing unconditional (modulo the layer-cake/weak-type
hypotheses of the Doob step):

  `∫ ∑_{i<n} |S i|^{p-2} v (i+1)
     ≤ (p/(p-1))^{p-2} (∫ V n^{p/2})^{2/p} (∫ |S n|^p)^{(p-2)/p}`,

the Rosenthal variance term `(∫ V n^{p/2})^{2/p}` (`V n = ∑ E[ξ_i² | F_{i-1}]`) paired with
the endpoint `L^p` norm.  No new external input; no new `Prop`; not imported by the root.
-/
import LatticeProb.Prob.BernsteinCrossTermBound
import LatticeProb.Prob.BernsteinDoobMaximal

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The conditional-variance pairing for the Rosenthal cross term.**  Composing the Doob
maximal inequality `doob_maximal_crossTermMax` with the cross-term bound gives the cumulative cross
term in terms of the predictable quadratic variation `V n = ∑_{i<n} v (i+1)` and the endpoint:

  `∫ ∑_{i<n} |S i|^{p-2} v (i+1)
     ≤ (p/(p-1))^{p-2} (∫ V n^{p/2})^{2/p} (∫ |S n|^p)^{(p-2)/p}`. -/
theorem crossTerm_le_variancePair [IsProbabilityMeasure μ] {ξ v : ℕ → Ω → ℝ} {p : ℝ}
    (hp : 2 < p) (n : ℕ) (hv : ∀ i, 0 ≤ᵐ[μ] v i)
    (hMmem : MemLp (fun ω => crossTermMax ξ n ω ^ (p - 2))
      (ENNReal.ofReal (p / (p - 2))) μ)
    (hVmem : MemLp (crossTermVariance v n) (ENNReal.ofReal (p / 2)) μ)
    (hintV : Integrable (fun ω => crossTermMax ξ n ω ^ (p - 2) * crossTermVariance v n ω) μ)
    (hintL : Integrable (fun ω => ∑ i ∈ Finset.range n,
      |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) μ)
    (hMint : Integrable (fun ω => crossTermMax ξ n ω ^ p) μ)
    (hweak : ∀ t : ℝ, 0 < t →
      (μ {ω | t ≤ crossTermMax ξ n ω}).toReal
        ≤ t⁻¹ * ∫ ω in {ω | t ≤ crossTermMax ξ n ω},
            |crossTermPartialSum ξ n ω| ∂μ)
    (hintD : Integrable (fun t : ℝ => p * t ^ (p - 1)
      * (μ {ω | t ≤ crossTermMax ξ n ω}).toReal) (volume.restrict (Set.Ioi 0)))
    (hboundD : Integrable (fun t : ℝ => p * t ^ (p - 2)
      * (∫ ω in {ω | t ≤ crossTermMax ξ n ω}, |crossTermPartialSum ξ n ω| ∂μ))
        (volume.restrict (Set.Ioi 0)))
    (hFubiniD : ∫ t in Set.Ioi 0, p * t ^ (p - 2)
        * (∫ ω in {ω | t ≤ crossTermMax ξ n ω}, |crossTermPartialSum ξ n ω| ∂μ)
      = (p / (p - 1)) * ∫ ω,
          |crossTermPartialSum ξ n ω| * crossTermMax ξ n ω ^ (p - 1) ∂μ)
    (hfmemD : MemLp (fun ω => |crossTermPartialSum ξ n ω|) (ENNReal.ofReal p) μ)
    (hMmemD : MemLp (fun ω => crossTermMax ξ n ω ^ (p - 1))
      (ENNReal.ofReal (p / (p - 1))) μ) :
    ∫ ω, (∑ i ∈ Finset.range n,
        |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω) ∂μ
      ≤ (p / (p - 1)) ^ (p - 2)
        * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p)
        * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ ((p - 2) / p) := by
  -- the Doob maximal inequality for the partial sums
  have hdoobL := doob_maximal_crossTermMax (ξ := ξ) (by linarith : (1 : ℝ) < p) n hMint
    hweak hintD hboundD hFubiniD hfmemD hMmemD
  have hAnn : (0 : ℝ) ≤ ∫ ω, crossTermMax ξ n ω ^ p ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (crossTermMax_nonneg ξ n ω) p)
  have hSnn : (0 : ℝ) ≤ ∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p)
  have hCp : (0 : ℝ) ≤ p / (p - 1) :=
    le_of_lt (div_pos (by linarith) (by linarith))
  -- raise the Doob bound to the `p`-th power
  have hx : ((∫ ω, crossTermMax ξ n ω ^ p ∂μ) ^ (1 / p)) ^ p
      = ∫ ω, crossTermMax ξ n ω ^ p ∂μ := by
    rw [← Real.rpow_mul hAnn (1 / p) p,
      show (1 : ℝ) / p * p = 1 by field_simp, Real.rpow_one]
  have hy : ((p / (p - 1)) * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ (1 / p)) ^ p
      = (p / (p - 1)) ^ p * ∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ := by
    rw [Real.mul_rpow hCp (Real.rpow_nonneg hSnn _),
      ← Real.rpow_mul hSnn (1 / p) p,
      show (1 : ℝ) / p * p = 1 by field_simp, Real.rpow_one]
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hAnn _) hdoobL (by linarith : (0 : ℝ) ≤ p)
  rw [hx, hy] at hpow
  exact crossTerm_le_variance_of_doob hp n hv hMmem hVmem hintV hintL hpow

end LatticeProb

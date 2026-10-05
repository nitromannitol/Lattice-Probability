/-
# The assembled Rosenthal bound for the martingale partial sums

`LatticeProb.crossTerm_le_variancePair` (`Prob/BernsteinVariancePair.lean`) bounds the cumulative
cross term by the conditional-variance term and the endpoint,

  `B = ∑_{i<n} ∫ |S i|^{p-2} v (i+1) ≤ K · (∫ V n^{p/2})^{2/p} · A^{(p-2)/p}`,
  `K = (p/(p-1))^{p-2}`, `A = ∫ |S n|^p`,

and `LatticeProb.martingaleOneStep_iterate` (`Prob/BernsteinInduction.lean`) telescopes the one-step
estimate into `A ≤ C (B + V)`, `V = ∑_{i<n} ∫ |ξ (i+1)|^p`.  Feeding these into
`LatticeProb.rosenthal_of_crossTerm` gives the actual Rosenthal bound with the source constants:

  `A^{2/p} ≤ max (2 C K · (∫ V n^{p/2})^{2/p}) ((2 C (K+1) V)^{2/p})`.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinVariancePair
import LatticeProb.Prob.BernsteinInduction

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The assembled Rosenthal bound.**  Given the telescoped one-step estimate `A ≤ C (B + V)`
(from `martingaleOneStep_iterate`) and the conditional-variance pairing
`B ≤ K (∫ V n^{p/2})^{2/p} A^{(p-2)/p}` (from `crossTerm_le_variancePair`), the endpoint
satisfies

  `A^{2/p} ≤ max (2 C K · (∫ V n^{p/2})^{2/p}) ((2 C (K+1) V)^{2/p})`. -/
theorem martingaleRosenthalBound [IsProbabilityMeasure μ] {ξ v : ℕ → Ω → ℝ} {p C K : ℝ}
    (hp : 2 ≤ p) (n : ℕ) (hv : ∀ i, 0 ≤ᵐ[μ] v i) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hiter : (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ)
      ≤ C * ((∑ i ∈ Finset.range n,
            ∫ ω, |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ)
        + ∑ i ∈ Finset.range n, ∫ ω, |ξ (i + 1) ω| ^ p ∂μ))
    (hpair : (∑ i ∈ Finset.range n,
          ∫ ω, |crossTermPartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ)
      ≤ K * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p)
        * (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ ((p - 2) / p)) :
    (∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ) ^ (2 / p)
      ≤ max (2 * (C * K) * (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p))
        ((2 * (C * (K + 1)
            * ∑ i ∈ Finset.range n, ∫ ω, |ξ (i + 1) ω| ^ p ∂μ)) ^ (2 / p)) := by
  have hA : (0 : ℝ) ≤ ∫ ω, |crossTermPartialSum ξ n ω| ^ p ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p)
  have hWnn : 0 ≤ᵐ[μ] crossTermVariance v n := by
    filter_upwards [ae_all_iff.mpr hv] with ω hω
    exact Finset.sum_nonneg fun i _ => hω (i + 1)
  have hW : (0 : ℝ) ≤ (∫ ω, crossTermVariance v n ω ^ (p / 2) ∂μ) ^ (2 / p) :=
    Real.rpow_nonneg
      (integral_nonneg_of_ae (hWnn.mono fun ω hω => Real.rpow_nonneg hω (p / 2))) _
  have hV : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, ∫ ω, |ξ (i + 1) ω| ^ p ∂μ :=
    Finset.sum_nonneg fun i _ =>
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p)
  exact rosenthal_of_crossTerm hp hA hW hC hK hiter
    (by linarith [hpair, mul_nonneg hK hV])

end LatticeProb

/-
# The conditional Bernstein mgf of the martingale sum

`LatticeProb.condExp_exp_sum_le` (`Prob/BernsteinFactorialAssemble.lean`) gives
`E[e^{λ ∑_{i<n} ξ_{i+1}} | F 0] ≤ᵐ e^{∑_{i<n} d_{i+1}}` from the per-increment conditional
mgf bounds `E[e^{λ ξ_{i+1}} | F i] ≤ᵐ e^{d_{i+1}}`.  The factorial-moment hypothesis
`∑_i E[|ξ_i|^q | F_{i-1}] ≤ (q!/2) a^{q-2} v` bounds the exponent sum by the Bernstein
exponent, `∑_{i<n} d_{i+1} ≤ λ²v/(2(1-aλ))`.  Composing the two gives the conditional
Bernstein mgf

  `E[e^{λ ∑_{i<n} ξ_{i+1}} | F 0] ≤ᵐ e^{λ²v/(2(1-aλ))}`,

which is exactly the hypothesis consumed by `LatticeProb.moment_le_of_condMgf`
(`Prob/BernsteinFactorialFinal.lean`) for the `r`-th moment bound `32(√(rv)+ra)`.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinFactorialAssemble

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The conditional Bernstein mgf of the martingale sum.**  Chaining the conditional product
bound with the exponent summation from the factorial-moment hypothesis: for `0 < 1 - aλ`, the
per-increment bounds `E[e^{λ ξ_{i+1}} | F i] ≤ᵐ e^{d_{i+1}}` and
`∑_{i<n} d_{i+1} ≤ λ²v/(2(1-aλ))` give

  `E[e^{λ ∑_{i<n} ξ_{i+1}} | F 0] ≤ᵐ e^{λ²v/(2(1-aλ))}`. -/
theorem condExp_exp_sum_mgf [IsProbabilityMeasure μ] {F : Filtration ℕ m₀}
    {ξ : ℕ → Ω → ℝ} {d : ℕ → ℝ} {lam a v : ℝ}
    (hf_int : ∀ i, Integrable (fun ω => Real.exp (lam * ξ i ω)) μ)
    (hfc : ∀ i, μ[fun ω => Real.exp (lam * ξ (i + 1) ω) | F i]
      ≤ᵐ[μ] fun _ => Real.exp (d (i + 1)))
    (hP_meas : ∀ n, StronglyMeasurable[F n]
      (fun ω => ∏ i ∈ Finset.range n, Real.exp (lam * ξ (i + 1) ω)))
    (hP_int : ∀ n, Integrable
      (fun ω => ∏ i ∈ Finset.range n, Real.exp (lam * ξ (i + 1) ω)) μ)
    (hP_nn : ∀ n, 0 ≤ᵐ[μ]
      fun ω => ∏ i ∈ Finset.range n, Real.exp (lam * ξ (i + 1) ω))
    (hPf_int : ∀ n, Integrable (fun ω =>
      (∏ i ∈ Finset.range n, Real.exp (lam * ξ (i + 1) ω))
        * Real.exp (lam * ξ (n + 1) ω)) μ)
    (hsum : ∀ n, ∑ i ∈ Finset.range n, d (i + 1) ≤ lam ^ 2 * v / (2 * (1 - a * lam))) :
    ∀ n, μ[fun ω => Real.exp (lam * ∑ i ∈ Finset.range n, ξ (i + 1) ω) | F 0]
      ≤ᵐ[μ] fun _ => Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
  intro n
  refine (condExp_exp_sum_le (F := F) (ξ := ξ) (d := d) (lam := lam)
    hf_int hfc hP_meas hP_int hP_nn hPf_int n).trans ?_
  exact Filter.Eventually.of_forall fun _ => Real.exp_le_exp.mpr (hsum n)

end LatticeProb

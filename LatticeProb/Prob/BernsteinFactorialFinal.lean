/-
# The factorial-Bernstein bound: conditional mgf to moment

The factorial-moment hypothesis `∑_i E[|ξ_i|^q | F_{i-1}] ≤ (q!/2) a^{q-2} v` governs the
**conditional** mgf of the sum `S = ∑_{i≤k} ξ_i` along the filtration `F`:

  `E[e^{λ S} | F 0] ≤ᵐ e^{λ²v/(2(1-aλ))}`,  `0 ≤ λ < 1/a`,

by the exponential-series/product argument, in which the exponent carries the summed factorial
moments `∑_i E[|ξ_i|^q | F_{i-1}]` (the landed `LatticeProb.condExp_exp_le_of_factorial` supplies the
per-increment series; the product over the filtration is what sums the exponents).

This file assembles that conditional bound with `LatticeProb.moment_le_of_mgf`
(`Prob/BernsteinFactorialBound.lean`): the tower property `∫ e^{λS} = ∫ E[e^{λS} | F 0]` turns the
conditional mgf into the unconditional one, and then Chernoff, the two-sided tail and the
tail-to-moment step give the actual factorial-Bernstein `r`-th moment bound

  `(∫ |S|^r dμ)^{1/r} ≤ 32 (√(r v) + r a)`.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinFactorialBound

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The factorial-Bernstein `r`-th moment bound from the conditional mgf.**  Let `F` be a
sub-σ-algebra of the ambient one, `S` a real random variable, and suppose that for `0 ≤ λ < 1/a`
the conditional mgf of `S` (and of `-S`) given `F` is bounded by `e^{λ²v/(2(1-aλ))}`.  Then, with
finite `L^r` integrability,

  `(∫ |S|^r dμ)^{1/r} ≤ 32 (√(r v) + r a)`. -/
theorem moment_le_of_condMgf [IsProbabilityMeasure μ] {F : MeasurableSpace Ω} (hmF : F ≤ m₀)
    {S : Ω → ℝ} {r a v : ℝ}
    (hr : 2 ≤ r) (ha : 0 < a) (hv : 0 < v)
    (hSint : Integrable (fun ω => |S ω| ^ r) μ)
    (hcond : ∀ lam : ℝ, 0 ≤ lam → lam * a < 1 →
      μ[fun ω => Real.exp (lam * S ω) | F] ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))))
    (hcond' : ∀ lam : ℝ, 0 ≤ lam → lam * a < 1 →
      μ[fun ω => Real.exp (lam * (-S ω)) | F] ≤ᵐ[μ]
        fun _ => Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))))
    (hexpint : ∀ lam : ℝ, 0 < lam → lam * a < 1 →
      Integrable (fun ω => Real.exp (lam * S ω)) μ)
    (hexpint' : ∀ lam : ℝ, 0 < lam → lam * a < 1 →
      Integrable (fun ω => Real.exp (lam * (-S ω))) μ)
    (hint : Integrable (fun t : ℝ => r * t ^ (r - 1)
      * (μ {ω | t ≤ |S ω|}).toReal) (volume.restrict (Set.Ioi 0)))
    (htailint : Integrable (fun t : ℝ => r * t ^ (r - 1)
      * (2 * Real.exp (-(t ^ 2 / (2 * (v + a * t)))))) (volume.restrict (Set.Ioi 0))) :
    (∫ ω, |S ω| ^ r ∂μ) ^ (1 / r) ≤ 32 * (Real.sqrt (r * v) + r * a) := by
  -- the tower property turns the conditional mgf into the unconditional one
  have huncond : ∀ lam : ℝ, 0 ≤ lam → lam * a < 1 →
      mgf S μ lam ≤ Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
    intro lam hlam0 hlam1
    rw [mgf, (integral_condExp hmF).symm]
    calc ∫ ω, (μ[fun ω' => Real.exp (lam * S ω') | F]) ω ∂μ
        ≤ ∫ _ω, Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) ∂μ :=
          integral_mono_ae integrable_condExp (integrable_const _) (hcond lam hlam0 hlam1)
      _ = Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
          rw [integral_const, probReal_univ, one_smul]
  have huncond' : ∀ lam : ℝ, 0 ≤ lam → lam * a < 1 →
      mgf (fun ω => -S ω) μ lam
        ≤ Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
    intro lam hlam0 hlam1
    rw [mgf, (integral_condExp hmF).symm]
    calc ∫ ω, (μ[fun ω' => Real.exp (lam * (-S ω')) | F]) ω ∂μ
        ≤ ∫ _ω, Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) ∂μ :=
          integral_mono_ae integrable_condExp (integrable_const _) (hcond' lam hlam0 hlam1)
      _ = Real.exp (lam ^ 2 * v / (2 * (1 - a * lam))) := by
          rw [integral_const, probReal_univ, one_smul]
  exact moment_le_of_mgf hr ha hv hSint huncond huncond' hexpint hexpint' hint htailint

end LatticeProb

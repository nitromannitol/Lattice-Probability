/-
# The conditional mgf of the sum from the per-increment bounds

`LatticeProb.condExp_prod_range_le` (`Prob/BernsteinFactorialFull.lean`) is the conditional
product/tower bound `E[∏_{i<n} f (i+1) | F 0] ≤ᵐ ∏_{i<n} c (i+1)`.  Specialising
`f i = e^{λ ξ_i}` and `c i = e^{d i}` and using
`∏ e^{λ ξ_{i+1}} = e^{λ ∑ ξ_{i+1}}`, it becomes the conditional mgf of the martingale sum

  `E[e^{λ ∑_{i<n} ξ_{i+1}} | F 0] ≤ᵐ e^{∑_{i<n} d_{i+1}}`

from the per-increment conditional mgf bounds `E[e^{λ ξ_{i+1}} | F i] ≤ᵐ e^{d_{i+1}}`.  This
is the step that the factorial-moment hypothesis feeds: `d_{i+1}` is the per-increment
Bernstein exponent and `∑_{i<n} d_{i+1} ≤ λ²v/(2(1-aλ))`.  The final moment bound is then
`LatticeProb.moment_le_of_condMgf`.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinFactorialFull

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The conditional mgf of the sum from the per-increment bounds.**  For a filtration `F`, a real
sequence `ξ`, exponents `d`, and `λ`, if each increment has conditional mgf
`E[e^{λ ξ_{i+1}} | F i] ≤ᵐ e^{d_{i+1}}`, then the conditional mgf of the partial sum satisfies

  `E[e^{λ ∑_{i<n} ξ_{i+1}} | F 0] ≤ᵐ e^{∑_{i<n} d_{i+1}}`. -/
theorem condExp_exp_sum_le [IsProbabilityMeasure μ] {F : Filtration ℕ m₀}
    {ξ : ℕ → Ω → ℝ} {d : ℕ → ℝ} {lam : ℝ}
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
        * Real.exp (lam * ξ (n + 1) ω)) μ) :
    ∀ n, μ[fun ω => Real.exp (lam * ∑ i ∈ Finset.range n, ξ (i + 1) ω) | F 0]
      ≤ᵐ[μ] fun _ => Real.exp (∑ i ∈ Finset.range n, d (i + 1)) := by
  intro n
  have hprod := condExp_prod_range_le
    (f := fun i ω => Real.exp (lam * ξ i ω)) (c := fun i => Real.exp (d i))
    hf_int (fun i => (Real.exp_pos (d i)).le) hfc hP_meas hP_int hP_nn hPf_int n
  have hLHS : (fun ω => ∏ i ∈ Finset.range n, Real.exp (lam * ξ (i + 1) ω))
      = fun ω => Real.exp (lam * ∑ i ∈ Finset.range n, ξ (i + 1) ω) := by
    funext ω
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  have hRHS : (fun _ : Ω => ∏ i ∈ Finset.range n, Real.exp (d (i + 1)))
      = fun _ : Ω => Real.exp (∑ i ∈ Finset.range n, d (i + 1)) := by
    funext ω
    rw [← Real.exp_sum]
  rw [hLHS, hRHS] at hprod
  exact hprod

end LatticeProb

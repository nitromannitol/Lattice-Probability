/-
# The conditional mgf product bound for a martingale filtration

The factorial-moment hypothesis controls the conditional mgf of each increment,
`E[e^{λ ξ_i} | F_{i-1}] ≤ e^{c_i}`.  To pass from the increments to the sum `S = ∑ ξ_i` one
uses
the **conditional product/tower bound**

  `E[∏_{i<n} e^{λ ξ_{i+1}} | F 0] ≤ᵐ[μ] ∏_{i<n} e^{c_{i+1}}`,

proved by induction: peel the last factor, apply the tower property to `F n`, pull the
`F n`-measurable partial product out of the conditional expectation, and bound the remaining
factor by `E[e^{λ ξ_{n+1}} | F n] ≤ c_{n+1}`.  This file is that lemma.

No new `Prop`; no new external input; no false Pinelis input; not imported by the root.
-/
import LatticeProb.Prob.BernsteinFactorialFinal

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The conditional product/tower bound.**  For a filtration `F`, non-negative `f i` with
`E[f (i+1) | F i] ≤ᵐ[μ] c (i+1)` (constant `c`), the conditional expectation of the partial
product
is bounded by the product of the constants:

  `E[∏_{i<n} f (i+1) | F 0] ≤ᵐ[μ] ∏_{i<n} c (i+1)`. -/
theorem condExp_prod_range_le [IsProbabilityMeasure μ] {F : Filtration ℕ m₀}
    {f : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hf_int : ∀ i, Integrable (f i) μ)
    (hc_nn : ∀ i, 0 ≤ c i)
    (hfc : ∀ i, μ[f (i + 1) | F i] ≤ᵐ[μ] fun _ => c (i + 1))
    (hP_meas : ∀ n, StronglyMeasurable[F n] (fun ω => ∏ i ∈ Finset.range n, f (i + 1) ω))
    (hP_int : ∀ n, Integrable (fun ω => ∏ i ∈ Finset.range n, f (i + 1) ω) μ)
    (hP_nn : ∀ n, 0 ≤ᵐ[μ] fun ω => ∏ i ∈ Finset.range n, f (i + 1) ω)
    (hPf_int : ∀ n, Integrable
      (fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * f (n + 1) ω) μ) :
    ∀ n, μ[fun ω => ∏ i ∈ Finset.range n, f (i + 1) ω | F 0]
      ≤ᵐ[μ] fun _ => ∏ i ∈ Finset.range n, c (i + 1) := by
  intro n
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.prod_empty]
      rw [condExp_const (F.le 0) (1 : ℝ)]
  | succ n ih =>
      have hPeel : (fun ω => ∏ i ∈ Finset.range (n + 1), f (i + 1) ω)
          = fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * f (n + 1) ω := by
        funext ω
        rw [Finset.prod_range_succ]
      rw [hPeel]
      -- tower to `F n`
      have htower : μ[fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * f (n + 1) ω | F 0]
          =ᵐ[μ] μ[μ[fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * f (n + 1) ω | F n]
            | F 0] :=
        (condExp_condExp_of_le (F.mono (Nat.zero_le n)) (F.le n)).symm
      -- pull the partial product out at level `F n`
      have hpull : μ[fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * f (n + 1) ω | F n]
          =ᵐ[μ] (fun ω => ∏ i ∈ Finset.range n, f (i + 1) ω)
            * μ[f (n + 1) | F n] :=
        condExp_mul_of_stronglyMeasurable_left (m := F n) (hP_meas n) (hPf_int n)
          (hf_int (n + 1))
      -- bound the last factor, using non-negativity of the partial product
      have hstep : μ[μ[fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * f (n + 1) ω | F n]
            | F 0]
          ≤ᵐ[μ] μ[fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * c (n + 1) | F 0] := by
        refine condExp_mono integrable_condExp (hP_int n |>.mul_const _) ?_
        filter_upwards [hpull, hfc n, hP_nn n] with ω e1 h1 h2
        rw [e1]
        simp only [Pi.mul_apply]
        exact mul_le_mul_of_nonneg_left h1 h2
      -- pull the constant out and apply the induction hypothesis
      have hconst : μ[fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * c (n + 1) | F 0]
          =ᵐ[μ] fun ω =>
            c (n + 1) * (μ[fun ω' => ∏ i ∈ Finset.range n, f (i + 1) ω' | F 0]) ω := by
        have heq : (fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * c (n + 1))
            = c (n + 1) • (fun ω => ∏ i ∈ Finset.range n, f (i + 1) ω) := by
          funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [heq]
        have hs := condExp_smul (μ := μ) (m := F 0) (c (n + 1))
          (fun ω => ∏ i ∈ Finset.range n, f (i + 1) ω)
        filter_upwards [hs] with ω hω
        simpa only [Pi.smul_apply, smul_eq_mul] using hω
      have hfinal : μ[fun ω => (∏ i ∈ Finset.range n, f (i + 1) ω) * c (n + 1) | F 0]
          ≤ᵐ[μ] fun _ => ∏ i ∈ Finset.range (n + 1), c (i + 1) := by
        rw [Finset.prod_range_succ]
        filter_upwards [hconst, ih] with ω h1 h2
        rw [h1, mul_comm (∏ i ∈ Finset.range n, c (i + 1)) (c (n + 1))]
        exact mul_le_mul_of_nonneg_left h2 (hc_nn (n + 1))
      exact (htower.le.trans (hstep.trans hfinal))

end LatticeProb

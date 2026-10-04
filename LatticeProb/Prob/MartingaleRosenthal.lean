/-
The conditional second-order step behind the martingale Rosenthal–Burkholder
inequality.

Pinelis's proof of
`(∫ |∑ ξ_i|^r)^{1/r} ≤ C (√r (∫ (∑ E[ξ_i² | F_{i-1}])^{r/2})^{1/r} + r a)`
proceeds by a one-step moment estimate.  Writing `S` for the partial sum (which is
measurable for the past `F`), `ξ` for the next martingale difference, and using the
pointwise second-order bound of `LatticeProb.exists_abs_add_rpow_bound`,

  `|S + ξ|^p ≤ |S|^p + p |S|^{p-2} S ξ + C (|S|^{p-2} ξ² + |ξ|^p)`,

the conditional expectation given `F` kills the linear term (because `S` is
`F`-measurable and `E[ξ | F] = 0`) and pulls the `F`-measurable factor out of the
quadratic term.  This file proves that conditional identity; integrating it gives
the one-step estimate `E|S + ξ|^p ≤ E|S|^p + C (E[|S|^{p-2} E[ξ² | F]] + E|ξ|^p)`
from which the Rosenthal–Burkholder bound is assembled by induction on `p`.

The conditional moment generating function that plays the same role in the
Bernstein (tail) route is `LatticeProb.condExp_exp_le` in `Prob/Freedman.lean`;
the pointwise input here is `LatticeProb.exists_abs_add_rpow_bound`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The linear term of the second-order bound is a martingale difference.**
If `S` is `m`-strongly-measurable, `E[ξ | m] = 0`, and `|S|^{p-2} S ξ` is integrable,
then `E[|S|^{p-2} S ξ | m] = 0`: the `m`-measurable factor `|S|^{p-2} S` pulls out of the
conditional expectation and annihilates `E[ξ | m]`. -/
theorem condExp_rpow_mul_mul_ae_eq_zero [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    {p : ℝ} {S ξ : Ω → ℝ}
    (hS : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2) * S ω)
    (hmean : μ[ξ | m] =ᵐ[μ] 0)
    (hint : Integrable (fun ω => |S ω| ^ (p - 2) * S ω * ξ ω) μ)
    (hξ : Integrable ξ μ) :
    μ[fun ω => |S ω| ^ (p - 2) * S ω * ξ ω | m] =ᵐ[μ] (0 : Ω → ℝ) := by
  change μ[(fun ω => |S ω| ^ (p - 2) * S ω) * ξ | m] =ᵐ[μ] (0 : Ω → ℝ)
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m) hS hint hξ
  filter_upwards [hpull, hmean] with ω e1 e2
  simp only [Pi.mul_apply, Pi.zero_apply] at e1 e2 ⊢
  rw [e1, e2, mul_zero]

/-- **The `m`-measurable factor pulls out of the quadratic term.**
For `S` with `|S|^{p-2}` `m`-strongly-measurable,
`E[|S|^{p-2} ξ² | m] = |S|^{p-2} E[ξ² | m]`. -/
private theorem condExp_rpow_mul_sq_ae_eq [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    {p : ℝ} {S ξ : Ω → ℝ}
    (hS : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2))
    (hint : Integrable (fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2) μ)
    (hξ2 : Integrable (fun ω => ξ ω ^ 2) μ) :
    μ[fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 | m]
      =ᵐ[μ] (fun ω => |S ω| ^ (p - 2)) * (μ[fun ω => ξ ω ^ 2 | m]) := by
  exact condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m) hS hint hξ2

/-- **The conditional second-order moment recursion for a martingale increment.**
Let `S` be measurable for the past `m`, let `ξ` be a martingale difference with
`μ[ξ | m] =ᵐ[μ] 0`, and let `p` be a real exponent.  Then the conditional expectation of
the right side of the pointwise bound `|S + ξ|^p ≤ |S|^p + p |S|^{p-2} S ξ + C (|S|^{p-2}
ξ² + |ξ|^p)` is the `m`-measurable function
`|S|^p + C (|S|^{p-2} μ[ξ² | m] + μ[|ξ|^p | m])`:
the linear term vanishes and the `m`-measurable factor `|S|^{p-2}` pulls out.  This is the
one-step estimate of Pinelis's Rosenthal–Burkholder induction. -/
theorem condExp_abs_add_rpow_eq [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {p C : ℝ} (S ξ : Ω → ℝ)
    (hAstrong : StronglyMeasurable[m] fun ω => |S ω| ^ p)
    (hfstrong : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2) * S ω)
    (hf2strong : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2))
    (hmean : μ[ξ | m] =ᵐ[μ] 0)
    (hA : Integrable (fun ω => |S ω| ^ p) μ)
    (hfξ : Integrable (fun ω => |S ω| ^ (p - 2) * S ω * ξ ω) μ)
    (hf2ξ2 : Integrable (fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2) μ)
    (hξ : Integrable ξ μ)
    (hξ2 : Integrable (fun ω => ξ ω ^ 2) μ)
    (hξp : Integrable (fun ω => |ξ ω| ^ p) μ) :
    μ[fun ω => |S ω| ^ p + p * (|S ω| ^ (p - 2) * S ω * ξ ω)
        + C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p) | m]
      =ᵐ[μ] fun ω => |S ω| ^ p
        + C * (|S ω| ^ (p - 2) * (μ[fun ω => ξ ω ^ 2 | m]) ω
          + (μ[fun ω => |ξ ω| ^ p | m]) ω) := by
  have h1 : μ[fun ω => |S ω| ^ p + p * (|S ω| ^ (p - 2) * S ω * ξ ω)
        + C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p) | m]
      =ᵐ[μ] μ[fun ω => |S ω| ^ p + p * (|S ω| ^ (p - 2) * S ω * ξ ω) | m]
        + μ[fun ω => C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p) | m] :=
    condExp_add (hA.add (hfξ.const_mul p))
      ((hf2ξ2.add hξp).const_mul C) m
  have h2 : μ[fun ω => |S ω| ^ p + p * (|S ω| ^ (p - 2) * S ω * ξ ω) | m]
      =ᵐ[μ] μ[fun ω => |S ω| ^ p | m]
        + μ[fun ω => p * (|S ω| ^ (p - 2) * S ω * ξ ω) | m] :=
    condExp_add hA (hfξ.const_mul p) m
  have h3 : μ[fun ω => |S ω| ^ p | m] =ᵐ[μ] fun ω => |S ω| ^ p :=
    Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm hAstrong hA)
  have h4 : μ[fun ω => p * (|S ω| ^ (p - 2) * S ω * ξ ω) | m] =ᵐ[μ] (0 : Ω → ℝ) := by
    have hsm := condExp_smul (μ := μ) (m := m) p
      (fun ω => |S ω| ^ (p - 2) * S ω * ξ ω)
    have hzero : μ[fun ω => p * (|S ω| ^ (p - 2) * S ω * ξ ω) | m]
        =ᵐ[μ] fun ω => p * (μ[fun ω => |S ω| ^ (p - 2) * S ω * ξ ω | m]) ω :=
      hsm
    have hlin := condExp_rpow_mul_mul_ae_eq_zero (μ := μ) hfstrong hmean hfξ hξ
    filter_upwards [hzero, hlin] with ω e1 e2
    simp only [Pi.zero_apply] at e2 ⊢
    rw [e1, e2, mul_zero]
  have h5 : μ[fun ω => C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p) | m]
      =ᵐ[μ] fun ω => C * (|S ω| ^ (p - 2) * (μ[fun ω => ξ ω ^ 2 | m]) ω
          + (μ[fun ω => |ξ ω| ^ p | m]) ω) := by
    have hq : μ[fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p | m]
        =ᵐ[μ] fun ω => |S ω| ^ (p - 2) * (μ[fun ω => ξ ω ^ 2 | m]) ω
          + (μ[fun ω => |ξ ω| ^ p | m]) ω := by
      have hsplit : μ[fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p | m]
          =ᵐ[μ] μ[fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 | m]
            + μ[fun ω => |ξ ω| ^ p | m] :=
        condExp_add hf2ξ2 hξp m
      have hpull := condExp_rpow_mul_sq_ae_eq (μ := μ) hf2strong hf2ξ2 hξ2
      filter_upwards [hsplit, hpull] with ω e1 e2
      simp only [Pi.add_apply, Pi.mul_apply] at e1 e2 ⊢
      rw [e1, e2]
    have hsm := condExp_smul (μ := μ) (m := m) C
      (fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p)
    have hscaled : μ[fun ω => C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p) | m]
        =ᵐ[μ] fun ω => C * (μ[fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p | m]) ω :=
      hsm
    filter_upwards [hscaled, hq] with ω e1 e2
    rw [e1, e2]
  filter_upwards [h1, h2, h3, h4, h5] with ω e1 e2 e3 e4 e5
  simp only [Pi.add_apply] at e1 e2 e5
  rw [e1, e2, e3, e4, e5]
  simp only [Pi.zero_apply]
  ring

end LatticeProb

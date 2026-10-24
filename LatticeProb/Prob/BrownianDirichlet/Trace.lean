import LatticeProb.Prob.BrownianPredictableTaylor
import LatticeProb.Prob.BrownianPathCoords

/-!
# Predictable Brownian Hessian trace

The conditional covariance of a Brownian increment contracts an integrable predictable
matrix to its trace. Scalar scaling contributes its square, and predictable linear
sums have zero expectation.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LatticeProb

/-- An integrable predictable matrix contracts against Brownian increments to its trace. -/
theorem standardBrownianLaw_integral_predictable_hessian {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (H : Fin d → Fin d → BrownianPath d → ℝ)
    (hH : ∀ i j, Measurable[brownianNaturalFiltration d t] (H i j))
    (hiH : ∀ i j, Integrable (H i j) μ) :
    (∫ ω, ∑ i, ∑ j, H i j ω *
      ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) ∂μ) =
      (s : ℝ) * ∫ ω, ∑ i, H i i ω ∂μ := by
  have hint (i j : Fin d) :=
    standardBrownianLaw_integrable_predictable_quadratic hμ t s (hH i j) (hiH i j) i j
  calc
    _ = ∑ i, ∑ j, (∫ ω, H i j ω ∂μ) * (if i = j then (s : ℝ) else 0) := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ ↦ hint i j)]
      apply Finset.sum_congr rfl
      intro j _
      exact standardBrownianLaw_integral_predictable_quadratic hμ t s (hH i j) i j
    _ = (s : ℝ) * ∑ i, ∫ ω, H i i ω ∂μ := by
      simp [Finset.mul_sum, mul_comm]
    _ = (s : ℝ) * ∫ ω, ∑ i, H i i ω ∂μ := by
      rw [integral_finsetSum _ (fun i _ ↦ hiH i i)]

/-- Scaling the actual Brownian increment by a real scalar multiplies its trace by
that scalar squared. The coefficient entries need only be integrable and predictable. -/
theorem standardBrownianLaw_integral_predictable_hessian_smul {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (σ : ℝ) (H : Fin d → Fin d → BrownianPath d → ℝ)
    (hH : ∀ i j, Measurable[brownianNaturalFiltration d t] (H i j))
    (hiH : ∀ i j, Integrable (H i j) μ) :
    (∫ ω, ∑ i, ∑ j, H i j ω *
      ((σ • (ω (t + s) - ω t)) i * (σ • (ω (t + s) - ω t)) j) ∂μ) =
      σ ^ 2 * (s : ℝ) * ∫ ω, ∑ i, H i i ω ∂μ := by
  have hscale (ω : BrownianPath d) :
      (∑ i, ∑ j, H i j ω *
        ((σ • (ω (t + s) - ω t)) i * (σ • (ω (t + s) - ω t)) j)) =
      σ ^ 2 * ∑ i, ∑ j, H i j ω *
        ((ω (t + s) i - ω t i) * (ω (t + s) j - ω t j)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  simp_rw [hscale]
  rw [integral_const_mul, standardBrownianLaw_integral_predictable_hessian hμ t s H hH hiH]
  ring

/-- A finite sum of integrable predictable linear coefficients against the next
Brownian increment has zero expectation. -/
theorem standardBrownianLaw_integral_predictable_linear_sum {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t s : ℝ≥0)
    (L : Fin d → BrownianPath d → ℝ)
    (hL : ∀ i, Measurable[brownianNaturalFiltration d t] (L i))
    (hiL : ∀ i, Integrable (L i) μ) :
    (∫ ω, ∑ i, L i ω * (ω (t + s) i - ω t i) ∂μ) = 0 := by
  rw [integral_finsetSum _ (fun i _ ↦
    standardBrownianLaw_integrable_predictable_linear hμ t s (hL i) (hiL i) i)]
  apply Finset.sum_eq_zero
  intro i _
  exact standardBrownianLaw_integral_predictable_linear hμ t s (hL i) i

end LatticeProb

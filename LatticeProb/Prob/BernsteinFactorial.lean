/-
# Bernstein Step E: the factorial-moment conditional moment generating function

This file proves the exponential-series step of the factorial-moment (Bernstein) route to
`Parking.External.Bernstein`; see `scratch/pk/bernstein-route.md`, Step E.

Given a centred martingale difference `X` whose conditional factorial moments satisfy
`μ[|X|^q | m] ≤ (q!/2) a^{q-2} v` for every `q ≥ 2`, the conditional moment generating function is

  `μ[exp (λ X) | m] ≤ exp (λ² v / (2 (1 - a λ)))`   for `0 ≤ λ` and `λ a < 1`.

The proof expands `exp (λ X)` in its factorial series, conditions term by term with the
conditional monotone convergence theorem `MeasureTheory.condExp_tsum`, bounds the `q ≥ 2` terms by
the factorial hypothesis, and sums the resulting geometric series.  The `q = 0, 1` terms contribute
`1` and `0`.
-/
import Mathlib
import LatticeProb.Prob.BernsteinMartingale

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- The factorial-series form of the exponential. -/
theorem exp_eq_tsum_factorial (x : ℝ) :
    Real.exp x = ∑' q : ℕ, x ^ q / (Nat.factorial q : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The factorial series with the Bernstein coefficients sums to the Bernstein exponent. -/
theorem tsum_factorial_bernstein {a v lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) (hlam_a : lam * a < 1) :
    ∑' q : ℕ, lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
        * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v)
      = lam ^ 2 * v / (2 * (1 - a * lam)) := by
  have hterm : ∀ q : ℕ, lam ^ (q + 2) / (Nat.factorial (q + 2) : ℝ)
        * ((Nat.factorial (q + 2) : ℝ) / 2 * a ^ q * v)
      = (lam ^ 2 * v / 2) * (lam * a) ^ q := by
    intro q
    have hf : (Nat.factorial (q + 2) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hlam_a]
  have hne : (1 : ℝ) - lam * a ≠ 0 := by linarith
  field_simp

end LatticeProb

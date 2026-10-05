/-
# Bernstein Step E: the factorial-moment exponential series

This file isolates the exponential-series step of the factorial-moment (Bernstein) route to
`Parking.External.Bernstein`; see `scratch/pk/bernstein-route.md`, Step E.

The intended step is: given a centred martingale difference `X` whose conditional factorial moments
satisfy `μ[|X|^q | m] ≤ (q!/2) a^{q-2} v` for every `q ≥ 2`, derive

  `μ[exp (λ X) | m] ≤ exp (λ² v / (2 (1 - a λ)))`   for `0 ≤ λ` and `λ a < 1`.

This file proves the two ingredients that are independent of the detailed integrability
bookkeeping:

* `exp_eq_tsum_factorial` — the factorial-series form of the exponential;
* `summable_factorial_series` — that series is summable;
* `tsum_factorial_bernstein` — the factorial series with the Bernstein coefficients sums to the
  Bernstein exponent `λ² v / (2 (1 - a λ))`;
* `condExp_exp_eq_tsum` — the **conditional interchange**: the conditional expectation of the
  exponential is the sum of the conditional expectations of its factorial-series terms, by the
  conditional monotone convergence theorem `MeasureTheory.condExp_tsum`.

Together these reduce Step E to the termwise comparison `μ[X^q | m] ≤ μ[|X|^q | m] ≤ (q!/2)a^{q-2}v`
(summed against the Bernstein series `tsum_factorial_bernstein`); that comparison and the final
`1 + c ≤ exp c` are the remaining bounded assembly.
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

/-- The factorial series of `x` is summable. -/
theorem summable_factorial_series (x : ℝ) :
    Summable (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) :=
  (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x).summable

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

/-- **Bernstein Step E, conditional interchange.**  The conditional expectation of the exponential
is the sum of the conditional expectations of its factorial-series terms, by the conditional
monotone convergence theorem `MeasureTheory.condExp_tsum`.  The summability hypothesis is exactly
the one required by `condExp_tsum`; for a factorial-moment bounded `X` it is supplied by the
integrability of `exp (λ |X|)`. -/
theorem condExp_exp_eq_tsum {m : MeasurableSpace Ω} (_hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable[m₀] X) (lam : ℝ)
    (hsum : ∑' q : ℕ, ∫⁻ ω, ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ ≠ ∞) :
    μ[fun ω => Real.exp (lam * X ω) | m]
      =ᵐ[μ] fun ω => ∑' q : ℕ,
        μ[fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ) | m] ω := by
  have hmeas : ∀ q, AEStronglyMeasurable[m₀]
      (fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ)) μ := by
    intro q
    exact (((hX.const_mul lam).pow_const q).div_const _).aestronglyMeasurable
  have h := condExp_tsum (μ := μ) (m := m)
    (f := fun q ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ)) hmeas hsum
  have hcongr : μ[fun ω => Real.exp (lam * X ω) | m]
      =ᵐ[μ] μ[fun ω => ∑' q : ℕ, (lam * X ω) ^ q / (Nat.factorial q : ℝ) | m] :=
    condExp_congr_ae (Filter.Eventually.of_forall fun ω => exp_eq_tsum_factorial _)
  exact hcongr.trans h

end LatticeProb

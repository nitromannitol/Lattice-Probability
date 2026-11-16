import LatticeProb.Prob.BernsteinFactorialSummability

/-!
# Integrability of factorial exponential series

Summable absolute integrated terms give both exponential integrability and the
summability condition for conditional interchange.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- An absolutely integrable factorial series yields an integrable exponential
and the extended-nonnegative summability needed for conditional interchange. -/
theorem integrable_exp_abs_of_summable_factorial_integrals {X : Ω → ℝ} {lam : ℝ}
    (hX : Measurable X)
    (hint : ∀ q : ℕ,
      Integrable (fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ)) μ)
    (hs : Summable (fun q : ℕ =>
      ∫ ω, ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ ∂μ)) :
    Integrable (fun ω => Real.exp |lam * X ω|) μ ∧
      (∑' q : ℕ, ∫⁻ ω, ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ) ≠ ∞ := by
  have hsum : (∑' q : ℕ, ∫⁻ ω,
      ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ ∂μ) ≠ ∞ := by
    simpa only [ofReal_integral_norm_eq_lintegral_enorm (hint _)] using hs.tsum_ofReal_ne_top
  refine ⟨?_, hsum⟩
  have hmeas : ∀ q : ℕ, AEMeasurable (fun ω =>
      ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ) μ :=
    fun q => (hint q).1.enorm
  have hpoint : ∀ ω, (∑' q : ℕ,
      ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖ₑ) =
      ENNReal.ofReal (Real.exp |lam * X ω|) := by
    intro ω
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div,
      ENNReal.ofReal_tsum_of_nonneg (fun q => by positivity)
        (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) _).summable]
    congr 1
    funext q
    simp [Real.enorm_eq_ofReal_abs, abs_div, abs_pow]
  have hfin : (∫⁻ ω, ENNReal.ofReal (Real.exp |lam * X ω|) ∂μ) ≠ ∞ := by
    rw [← lintegral_tsum hmeas] at hsum
    simpa only [hpoint] using hsum
  exact (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop : AEStronglyMeasurable (fun ω => Real.exp |lam * X ω|) μ)
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).mp hfin

end LatticeProb

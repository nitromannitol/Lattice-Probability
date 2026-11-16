import LatticeProb.Prob.BernsteinFactorialBudget

/-!
# Conditional exponential series

The predictable absolute-moment series controls the conditional exponential series.
-/

open MeasureTheory Filter Finset

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- Summability of the conditional absolute-moment series implies summability of the
conditional exponential series. -/
theorem summable_condExp_factorialSeries [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} {X : Ω → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hg : ∀ᵐ ω ∂μ, Summable (fun q : ℕ => if q < 2 then 0 else
      (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω)) :
    ∀ᵐ ω ∂μ, Summable (fun q : ℕ =>
      (μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω) := by
  have hb : ∀ q : ℕ, ∀ᵐ ω ∂μ,
      ‖(μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω‖ ≤
      (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω := by
    intro q
    have hnorm := norm_condExp_le (μ := μ) (m := m)
      (fun ω => (lam * X ω) ^ q / (Nat.factorial q : ℝ))
    have heq : (fun ω => ‖(lam * X ω) ^ q / (Nat.factorial q : ℝ)‖) =
        (lam ^ q / (Nat.factorial q : ℝ)) • (fun ω => |X ω| ^ q) := by
      funext ω
      simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, abs_of_nonneg hlam,
        Nat.abs_cast, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq] at hnorm
    have hsm := condExp_smul (μ := μ) (lam ^ q / (Nat.factorial q : ℝ))
      (fun ω => |X ω| ^ q) m
    filter_upwards [hnorm, hsm] with ω hnormω hsmω
    exact hnormω.trans_eq (by simpa only [Pi.smul_apply, smul_eq_mul] using hsmω)
  have hall : ∀ᵐ ω ∂μ, ∀ q : ℕ,
      ‖(μ[fun ω' => (lam * X ω') ^ q / (Nat.factorial q : ℝ) | m]) ω‖ ≤
      (lam ^ q / (Nat.factorial q : ℝ)) * (μ[fun ω' => |X ω'| ^ q | m]) ω :=
    ae_all_iff.mpr hb
  filter_upwards [hg, hall] with ω hgω hallω
  apply hgω.of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 2] with q hq
  simpa only [ite_eq_right (not_lt.mpr hq)] using hallω q

end LatticeProb

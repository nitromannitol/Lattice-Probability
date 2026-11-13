/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBX0Slope at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Slope

 




set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise Exponent.AnnularRecursion

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

 
theorem laneB_reference_slope (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ α : ℝ, Tendsto (fun n : ℕ =>
      (Real.logb 2 (lambdaN ξ W P n) + α * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨Cm, hCm, hmom⟩ := moment_package hW hξ
  obtain ⟨Crec, hCrec, hrec⟩ := real_recursion hW hξ hCm hmom
  set EU : ℕ → ℝ := fun n =>
    (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ∂P).toReal
  set EU2 : ℕ → ℝ := fun n =>
    (∫⁻ ω, Exponent.PolygonalCost.polyAnnularCost ξ (fun x => phiMN W P 0 n x ω) ^ 2 ∂P).toReal
  set μ : ℕ → ℝ := fun n => if n = 0 then lambdaN ξ W P 0 else EU n with hμ
  set M₂ : ℕ → ℝ := fun n => if n = 0 then lambdaN ξ W P 0 ^ 2 else EU2 n with hM₂
  have hlam := lambdaN_pos' hW ξ
  have hgL : ∀ n : ℕ, Real.exp (-(Cm * Real.sqrt n + Cm)) * lambdaN ξ W P n ≤ μ n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [hμ, ite_eq_left rfl, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add]
      have : Real.exp (-Cm) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      nlinarith [hlam 0]
    · simp only [hμ, ite_eq_right hn]
      exact (hmom n (Nat.one_le_iff_ne_zero.2 hn)).2.2.1
  have hgU : ∀ n : ℕ, μ n ≤ Real.exp (Cm * Real.sqrt n + Cm) * lambdaN ξ W P n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [hμ, ite_eq_left rfl, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add]
      have : 1 ≤ Real.exp Cm := Real.one_le_exp hCm
      nlinarith [hlam 0]
    · simp only [hμ, ite_eq_right hn]
      exact (hmom n (Nat.one_le_iff_ne_zero.2 hn)).2.2.2.1
  have hgS : ∀ n : ℕ, M₂ n ≤ (Real.exp (Cm * Real.sqrt n + Cm) * lambdaN ξ W P n) ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [hM₂, ite_eq_left rfl, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_add]
      have : 1 ≤ Real.exp Cm := Real.one_le_exp hCm
      have h0 := hlam 0
      have h1 : lambdaN ξ W P 0 ≤ Real.exp Cm * lambdaN ξ W P 0 := by nlinarith
      exact pow_le_pow_left₀ h0.le h1 2
    · simp only [hM₂, ite_eq_right hn]
      exact (hmom n (Nat.one_le_iff_ne_zero.2 hn)).2.2.2.2
  obtain ⟨Kl, -, hlow⟩ :=
    Exponent.LinearLower.annular_mean_logb_linear_lower_of_moment_lower hW hξ.le μ Cm hCm hgL
  have hsplit : ∀ m k : ℕ, 8 ≤ m → 1 ≤ k →
      μ (m + k) ≤
        Crec * Real.exp (Crec * ((m + k : ℕ) : ℝ) ^ (2 / 3 : ℝ)) * μ m * μ k +
        0 * Real.exp (1 * Real.sqrt (m + k : ℕ) - 1 * ((m + k : ℕ) : ℝ) ^ (4 / 3 : ℝ)) *
          μ (m + k) := by
    intro m k hm hk
    have hmk : m + k ≠ 0 := by omega
    have hm0 : m ≠ 0 := by omega
    have hk0 : k ≠ 0 := by omega
    simp only [hμ, ite_eq_right hmk, ite_eq_right hm0, ite_eq_right hk0, zero_mul, add_zero]
    exact hrec m k hm hk
  exact Exponent.SlopeAssembly.dyadic_median_slope_of_analytic_summaries μ (lambdaN ξ W P) M₂ Cm Crec 0 1 1 Kl
    hCm hCrec le_rfl zero_le_one one_pos hlam hgL hgU hgS hlow hsplit


end SupercriticalLQGUniqueness.B2.DG20Conc

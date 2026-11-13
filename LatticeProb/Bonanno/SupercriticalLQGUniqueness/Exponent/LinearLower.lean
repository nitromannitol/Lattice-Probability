/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.LinearLower at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6XiQ




 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace SupercriticalLQGUniqueness.Exponent.LinearLower
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem annular_mean_logb_linear_lower_of_moment_lower
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (μ : ℕ → ℝ) (Cmom : ℝ) (hCmom : 0 ≤ Cmom)
    (hgeomLower : ∀ n : ℕ,
      Real.exp (-(Cmom * Real.sqrt n + Cmom)) * lambdaN ξ W P n ≤ μ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
      -K * (n : ℝ) ≤ Real.logb 2 (μ n) := by
  let B : ℝ := SupTail.ferniqueCF * Real.sqrt 6 + 4 * Real.log 2 + 1
  have hCF := SupTail.ferniqueCF_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K : ℝ := (2 * Cmom + ξ * B) / Real.log 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLam := S6XiQ.lambdaN_ge_inf_field hW hξ hn
  have hE : 0 < Real.exp (-(ξ * (SupTail.ferniqueCF * Real.sqrt 6 +
      (2 * (n + 1) * Real.log 2 + 1)))) := Real.exp_pos _
  have hLamPos : 0 < lambdaN ξ W P n := hE.trans_le hLam
  have hMuPos : 0 < μ n := (mul_pos (Real.exp_pos _) hLamPos).trans_le (hgeomLower n)
  have hsize : SupTail.ferniqueCF * Real.sqrt 6 +
      (2 * (n + 1) * Real.log 2 + 1) ≤ B * (n : ℝ) := by
    dsimp [B]
    have hF : 0 ≤ SupTail.ferniqueCF * Real.sqrt 6 := by positivity
    nlinarith [hlog2.le, hF]
  have hsqrt : Real.sqrt (n : ℝ) ≤ n := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]
  have hR : Cmom * Real.sqrt n + Cmom ≤ 2 * Cmom * (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hCmom]
  have hprod : Real.exp (-(Cmom * Real.sqrt n + Cmom)) *
      Real.exp (-(ξ * (SupTail.ferniqueCF * Real.sqrt 6 +
      (2 * (n + 1) * Real.log 2 + 1)))) ≤ μ n :=
    (mul_le_mul_of_nonneg_left hLam (Real.exp_pos _).le).trans (hgeomLower n)
  rw [← Real.exp_add] at hprod
  have hlog := Real.log_le_log (Real.exp_pos _) hprod
  rw [Real.log_exp] at hlog
  have hlow : -((2 * Cmom + ξ * B) * (n : ℝ)) ≤ Real.log (μ n) := by
    nlinarith [mul_le_mul_of_nonneg_left hsize hξ, hR]
  rw [Real.logb]
  apply (le_div_iff₀ hlog2).2
  dsimp [K]
  field_simp
  nlinarith [hlow]



end SupercriticalLQGUniqueness.Exponent.LinearLower

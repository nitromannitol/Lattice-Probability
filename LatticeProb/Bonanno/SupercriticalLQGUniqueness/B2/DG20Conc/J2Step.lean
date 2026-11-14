/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J2Step at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2VarCond
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2VarianceOfCondExp

 








set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise J2Defs J2Inputs

 
theorem j2_efron_rate_le_one (N a : ℝ) (hN : 0 ≤ N) (ha : 0 < a) :
    ∃ K₁ : ℕ, ∀ K : ℕ, K₁ ≤ K →
      N * Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3)) * (2 : ℝ) ^ (-(a * K)) ≤ 1 := by
  set c : ℝ := a * Real.log 2 with hc
  have hc0 : 0 < c := mul_pos ha (Real.log_pos (by norm_num))
  set M : ℝ := (2 / c) ^ (3 : ℕ) with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨K₁, hK₁⟩ := exists_nat_ge (M + 2 * Real.log (N + 1) / c + 1)
  refine ⟨K₁, fun K hK => ?_⟩
  have hKr : M + 2 * Real.log (N + 1) / c + 1 ≤ (K : ℝ) := hK₁.trans (by exact_mod_cast hK)
  have hlN : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith)
  have hKM : M ≤ (K : ℝ) := by
    have : 0 ≤ 2 * Real.log (N + 1) / c := by positivity
    linarith
  have hK0 : 0 < (K : ℝ) := lt_of_lt_of_le hM0 hKM
  
  have hpow : (K : ℝ) ^ ((2 : ℝ) / 3) ≤ c / 2 * K := by
    have hsplit : (K : ℝ) ^ ((2 : ℝ) / 3) = (K : ℝ) * (K : ℝ) ^ (-(1 : ℝ) / 3) := by
      rw [show (2 : ℝ) / 3 = 1 + (-(1 : ℝ) / 3) by norm_num, Real.rpow_add hK0, Real.rpow_one]
    have hMr : M ^ (-(1 : ℝ) / 3) = c / 2 := by
      rw [hM, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      rw [Real.rpow_neg_one, inv_div]
    have hle : (K : ℝ) ^ (-(1 : ℝ) / 3) ≤ M ^ (-(1 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_nonpos hM0 hKM (by norm_num)
    rw [hsplit, hMr] at *
    calc (K : ℝ) * (K : ℝ) ^ (-(1 : ℝ) / 3) ≤ (K : ℝ) * (c / 2) :=
          mul_le_mul_of_nonneg_left (hMr ▸ hle) hK0.le
      _ = c / 2 * K := by ring
  have h2 : (2 : ℝ) ^ (-(a * K)) = Real.exp (-(c * K)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hc]; ring_nf
  have hexp : Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3)) * Real.exp (-(c * K)) ≤
      Real.exp (-Real.log (N + 1)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h3 : 2 * Real.log (N + 1) / c ≤ (K : ℝ) := by
      have : 0 ≤ M := hM0.le
      linarith
    have h4 : Real.log (N + 1) ≤ c / 2 * K := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ c / 2)
      have e : c / 2 * (2 * Real.log (N + 1) / c) = Real.log (N + 1) := by field_simp
      linarith
    linarith
  have hN1 : Real.exp (-Real.log (N + 1)) = (N + 1)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log (by linarith)]
  rw [h2, mul_assoc]
  calc N * (Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3)) * Real.exp (-(c * K)))
      ≤ N * (N + 1)⁻¹ := by rw [← hN1]; exact mul_le_mul_of_nonneg_left hexp hN
    _ ≤ 1 := by
        rw [mul_inv_le_iff₀ (by linarith)]; linarith

 


theorem j2_step_of_efronFactors (ξ : Ioi (0 : ℝ)) (Qψ : PsiParams) (hQ : PsiSmall Qψ) {p : ℝ}
    (hEF : EfronFactors ξ Qψ p) (C : ℝ) (hC : 0 ≤ C) :
    ∃ K₁ : ℕ, ∀ K : ℕ, K₁ ≤ K →
      ∀ {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∀ k : ℕ, K ≤ k →
        LambdaN (ξ : ℝ) W P (k - K) (ENNReal.ofReal p) ≤ Real.exp (C * Real.sqrt (K : ℝ)) →
        Var[L24.logLenPsi (ξ : ℝ) Qψ W P k; P] ≤ ((ξ : ℝ) ^ 2 * Real.log 2 + 1) * K := by
  obtain ⟨N₁, N₂, a, K₀, ha, hEFC⟩ := hEF C hC
  obtain ⟨K₂, hK₂⟩ := j2_efron_rate_le_one (|N₁| * |N₂|) a (by positivity) ha
  refine ⟨max K₀ K₂, fun K hK => ?_⟩
  intro Ω _ _ P _ W hW k hKk hH
  have hE := hEFC P W hW K k ((le_max_left _ _).trans hK) hKk hH
  have hvar := j2_var_condExp_le_of_efronFactorsAt P W hW Qψ hQ (ξ : ℝ) hKk
    (sq_nonneg _) (sq_nonneg _) hE
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at hvar
  have hrate := hK₂ K ((le_max_right _ _).trans hK)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hbound : |N₂ * (2 : ℝ) ^ (-(a * K))| *
      |N₁ * K * Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3))| ≤ K := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
      abs_of_nonneg hK0, abs_of_nonneg (Real.exp_pos _).le]
    calc |N₂| * (2 : ℝ) ^ (-(a * K)) * (|N₁| * K * Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3)))
        = (|N₁| * |N₂| * Real.exp ((K : ℝ) ^ ((2 : ℝ) / 3)) * (2 : ℝ) ^ (-(a * K))) * K := by
          ring
      _ ≤ 1 * K := mul_le_mul_of_nonneg_right hrate hK0
      _ = K := one_mul _
  have h := j2_log_variance_le_of_condExp_bound P W hW Qψ (ξ : ℝ) hKk _ (hvar.trans hbound)
  calc Var[L24.logLenPsi (ξ : ℝ) Qψ W P k; P] ≤ (ξ : ℝ) ^ 2 * (K * Real.log 2) + K := h
    _ = ((ξ : ℝ) ^ 2 * Real.log 2 + 1) * K := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc

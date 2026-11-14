/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceLoglog at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceUpperAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_source_loglog_ge_one (Q : PsiParams) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, 2 ≤ K →
      ∀ T : ℝ,
        (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T →
          1 ≤ Real.log (Real.log T) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K₀, hK₀⟩ := j1_eventually_large_power Q
    (Real.exp 1 / Real.log 2)
  refine ⟨K₀, ?_⟩
  intro K hK hK2 T hT
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hαβ : ((K : ℝ)^((1 / 2 : ℝ) + 2 * Q.ε₀)) ≤
      (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) :=
    Real.rpow_le_rpow_of_exponent_le hKr (by linarith [Q.ε₀_pos])
  have hpow : Real.exp 1 <
      (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) * Real.log 2 := by
    have hh := mul_lt_mul_of_pos_right (hK₀ K hK) hl2
    have he : (Real.exp 1 / Real.log 2) * Real.log 2 = Real.exp 1 := by
      field_simp [ne_of_gt hl2]
    nlinarith [mul_le_mul_of_nonneg_right hαβ hl2.le]
  have ha : 0 < (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hTpos : 0 < T := ha.trans hT
  have hlogT :
      (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) * Real.log 2 < Real.log T := by
    have hh := (Real.log_lt_log_iff ha hTpos).mpr hT
    simpa only [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] using hh
  have hll : 1 < Real.log (Real.log T) := by
    have hh := Real.log_lt_log (Real.exp_pos 1) (hpow.trans hlogT)
    simpa only [Real.log_exp] using hh
  exact hll.le

end SupercriticalLQGUniqueness.B2.DG20Conc

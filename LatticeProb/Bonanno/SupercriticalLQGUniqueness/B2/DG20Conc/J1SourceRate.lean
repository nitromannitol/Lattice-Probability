/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundScaleRange

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_source_lower_rate (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 2 ≤ K) (B T c : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hc : 0 < c)
    (hD : (1 + |ξ| * B)^2 ≤ j1CommonDenominator ξ Q K) :
    Real.exp (-c * (Real.log (j1CoarseTailParameter ξ B T))^2) ≤
      Real.exp (-(c / (1 + 5 * |ξ|)^2) * (Real.log T)^2 /
        (K : ℝ)^(3 * Q.ε₀)) := by
  have hM := j1_common_denominator_pos ξ Q K (by omega)
  have hh := j1_coarse_exp_lower ξ B T (j1CommonDenominator ξ Q K) c
    hB hT hM hc.le hD
  convert hh using 1
  dsimp [j1CommonDenominator]
  have hA : (1 + 5 * |ξ|)^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (by positivity))
  have hpow : (K : ℝ)^(3 * Q.ε₀) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < K)) _)
  field_simp [hA, hpow]

theorem j1_source_upper_rate (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 2 ≤ K) (B T c : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hc : 0 < c)
    (hD : (1 + |ξ| * B)^2 ≤ j1CommonDenominator ξ Q K)
    (hs : 3 < j1CoarseTailParameter ξ B T) :
    Real.exp (-c * (Real.log (j1CoarseTailParameter ξ B T))^2 /
      Real.log (Real.log (j1CoarseTailParameter ξ B T))) ≤
      Real.exp (-(c / (1 + 5 * |ξ|)^2) * (Real.log T)^2 /
        ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))) := by
  have hM := j1_common_denominator_pos ξ Q K (by omega)
  have hh := j1_coarse_exp_loglog_lower ξ B T
    (j1CommonDenominator ξ Q K) c hB hT hM hc.le hD hs
  convert hh using 1
  dsimp [j1CommonDenominator]
  have hA : (1 + 5 * |ξ|)^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (by positivity))
  have hpow : (K : ℝ)^(3 * Q.ε₀) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < K)) _)
  have hll : Real.log (Real.log T) ≠ 0 := by
    have h3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hT3 : 3 < T := by
      have hD1 : 1 ≤ 1 + |ξ| * B := by
        nlinarith [mul_nonneg (abs_nonneg ξ) hB]
      have hT1 : 1 ≤ T := by
        by_contra h
        have ht1 : T ≤ 1 := le_of_not_ge h
        have hsle : j1CoarseTailParameter ξ B T ≤ 1 :=
          Real.rpow_le_one hT.le ht1
            (div_nonneg (by norm_num) (by linarith : 0 ≤ 1 + |ξ| * B))
        linarith
      have hsT : j1CoarseTailParameter ξ B T ≤ T :=
        Real.rpow_le_self_of_one_le hT1
          ((div_le_iff₀ (by linarith : 0 < 1 + |ξ| * B)).2 (by linarith))
      linarith
    exact ne_of_gt (Real.log_pos (h3.trans (Real.log_lt_log (by norm_num) hT3)))
  field_simp [hA, hpow, hll]

end SupercriticalLQGUniqueness.B2.DG20Conc

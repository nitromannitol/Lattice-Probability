/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceUpperRateMono at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceLowerAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_source_upper_rate_of_le (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 2 ≤ K) (B T c d : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hc : 0 < c)
    (hdc : d ≤ c)
    (hD : (1 + |ξ| * B)^2 ≤ j1CommonDenominator ξ Q K)
    (hs : 3 < j1CoarseTailParameter ξ B T)
    (hll : 0 < Real.log (Real.log T)) :
    Real.exp (-c * (Real.log (j1CoarseTailParameter ξ B T))^2 /
      Real.log (Real.log (j1CoarseTailParameter ξ B T))) ≤
      Real.exp (-(d / (1 + 5 * |ξ|)^2) * (Real.log T)^2 /
        ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))) := by
  have hbase := j1_source_upper_rate ξ Q K hK B T c hB hT hc hD hs
  have hA : 0 < (1 + 5 * |ξ|)^2 := sq_pos_of_pos (by positivity)
  have hpow : 0 < (K : ℝ)^(3 * Q.ε₀) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < K)) _
  have hcoef : d / (1 + 5 * |ξ|)^2 ≤ c / (1 + 5 * |ξ|)^2 :=
    div_le_div_of_nonneg_right hdc hA.le
  have hL : 0 ≤ (Real.log T)^2 /
      ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg hpow.le hll.le)
  have hmul := mul_le_mul_of_nonneg_right hcoef hL
  exact hbase.trans (Real.exp_le_exp.mpr (by
    calc
      -(c / (1 + 5 * |ξ|)^2) * (Real.log T)^2 /
          ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)) =
        -((c / (1 + 5 * |ξ|)^2) *
          ((Real.log T)^2 /
            ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := by ring
      _ ≤ -((d / (1 + 5 * |ξ|)^2) *
          ((Real.log T)^2 /
            ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := neg_le_neg hmul
      _ = -(d / (1 + 5 * |ξ|)^2) * (Real.log T)^2 /
          ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)) := by ring))

end SupercriticalLQGUniqueness.B2.DG20Conc

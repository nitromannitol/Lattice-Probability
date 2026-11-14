/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CommonDenominator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseRate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

def j1CommonDenominator (ξ : ℝ) (Q : PsiParams) (K : ℕ) : ℝ :=
  (1 + 5 * |ξ|)^2 * (K : ℝ)^(3 * Q.ε₀)

theorem j1_common_denominator_pos (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 1 ≤ K) :
    0 < j1CommonDenominator ξ Q K := by
  dsimp [j1CommonDenominator]
  have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  positivity

theorem j1_small_denominator_bound (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 2 ≤ K) :
    (1 + |ξ| * 5)^2 ≤ j1CommonDenominator ξ Q K := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hpow : 1 ≤ (K : ℝ)^(3 * Q.ε₀) :=
    Real.one_le_rpow hKr (by linarith [Q.ε₀_pos])
  dsimp [j1CommonDenominator]
  have hA : 0 ≤ (1 + 5 * |ξ|)^2 := sq_nonneg _
  nlinarith [mul_nonneg hA (sub_nonneg.mpr hpow)]

theorem j1_round_denominator_bound (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 2 ≤ K) :
    (1 + |ξ| * (2 : ℝ)^(laneBCoarseIndex Q K + 1))^2 ≤
      j1CommonDenominator ξ Q K := by
  have hprev := j1_coarse_denominator_bound ξ Q K hK
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hpow : 0 ≤ (K : ℝ)^(3 * Q.ε₀) :=
    (Real.rpow_pos_of_pos (by linarith [hKr]) _).le
  have hcoeff : (1 + 4 * |ξ|)^2 ≤ (1 + 5 * |ξ|)^2 := by
    nlinarith [abs_nonneg ξ,
      mul_nonneg (by nlinarith [abs_nonneg ξ] : 0 ≤ |ξ|)
        (by nlinarith [abs_nonneg ξ] : 0 ≤ 2 + 9 * |ξ|)]
  dsimp [j1CommonDenominator]
  exact hprev.trans (mul_le_mul_of_nonneg_right hcoeff hpow)

end SupercriticalLQGUniqueness.B2.DG20Conc

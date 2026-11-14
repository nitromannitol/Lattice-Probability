/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseDenominator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseRadiusBound

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_coarse_denominator_bound (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 2 ≤ K) :
    (1 + |ξ| * (2 : ℝ)^(laneBCoarseIndex Q K + 1))^2 ≤
      (1 + 4 * |ξ|)^2 * (K : ℝ)^(3 * Q.ε₀) := by
  let x := (K : ℝ)^Q.ε₀
  let B := (2 : ℝ)^(laneBCoarseIndex Q K + 1)
  let A := 1 + 4 * |ξ|
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hx : 1 ≤ x := Real.one_le_rpow hKr Q.ε₀_pos.le
  have hB : B < 4 * x := j1_coarse_radius_lt_four_power Q K hK
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ 1 + |ξ| * B := by dsimp [B]; positivity
  have hDA : 1 + |ξ| * B ≤ A * x := by
    dsimp [A]
    have hgap : 0 ≤ 4 * x - B := by linarith
    nlinarith [mul_nonneg (abs_nonneg ξ) hgap]
  have hx3 : x^2 ≤ x^3 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]
  have hsq : (1 + |ξ| * B)^2 ≤ A^2 * x^2 := by
    have hx0 : 0 ≤ x := by linarith
    have hsum : 0 ≤ A * x + (1 + |ξ| * B) :=
      add_nonneg (mul_nonneg hA hx0) hD
    nlinarith [mul_nonneg (sub_nonneg.mpr hDA) hsum]
  have hA2 : 0 ≤ A^2 := sq_nonneg A
  have he : x^3 = (K : ℝ)^(3 * Q.ε₀) := by
    dsimp [x]
    calc
      ((K : ℝ)^Q.ε₀)^3 = ((K : ℝ)^Q.ε₀)^(3 : ℝ) :=
        (Real.rpow_natCast _ 3).symm
      _ = (K : ℝ)^(Q.ε₀ * 3) := by
        rw [Real.rpow_mul (by linarith [hKr])]
      _ = (K : ℝ)^(3 * Q.ε₀) := by ring
  dsimp [B, A] at *
  rw [← he]
  exact hsq.trans (mul_le_mul_of_nonneg_left hx3 hA2)

end SupercriticalLQGUniqueness.B2.DG20Conc

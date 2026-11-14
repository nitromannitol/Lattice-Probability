/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1GaussianUpperRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceUpperRateMono

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

theorem j1_gaussian_to_source_upper_rate (ξ : ℝ) (Q : PsiParams)
    (K : ℕ) (hK : 2 ≤ K) (B T c d : ℝ)
    (hB : 0 ≤ B) (hT : 0 < T) (hc : 0 < c)
    (hd : 0 < d) (hdc : d ≤ c)
    (hD : (1 + |ξ| * B)^2 ≤ j1CommonDenominator ξ Q K)
    (hll : 1 ≤ Real.log (Real.log T)) :
    Real.exp (-c * (Real.log (j1CoarseTailParameter ξ B T))^2) ≤
      Real.exp (-(d / (1 + 5 * |ξ|)^2) * (Real.log T)^2 /
        ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))) := by
  have hbase := j1_source_lower_rate_of_le ξ Q K hK B T c d
    hB hT hc hdc hD
  have hA : 0 < (1 + 5 * |ξ|)^2 := sq_pos_of_pos (by positivity)
  have hpow : 0 < (K : ℝ)^(3 * Q.ε₀) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < K)) _
  let a := d / (1 + 5 * |ξ|)^2
  let X := (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀)
  let L := Real.log (Real.log T)
  have ha : 0 < a := div_pos hd hA
  have hX : 0 ≤ X := div_nonneg (sq_nonneg _) hpow.le
  have hL : 0 < L := by dsimp [L]; linarith
  have hdiv : X / L ≤ X := by
    apply (div_le_iff₀ hL).2
    nlinarith [mul_nonneg hX (sub_nonneg.mpr hll)]
  have he : -a * X / L = -(d / (1 + 5 * |ξ|)^2) *
      (Real.log T)^2 /
      ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)) := by
    dsimp [a, X, L]
    field_simp [ne_of_gt hpow, ne_of_gt hL, ne_of_gt hA]
  have hrate : Real.exp (-a * X) ≤ Real.exp (-a * X / L) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hdiv ha.le
    calc
      -a * X = -(a * X) := by ring
      _ ≤ -(a * (X / L)) := neg_le_neg hh
      _ = -a * X / L := by ring
  have he0 : -a * X = -(d / (1 + 5 * |ξ|)^2) *
      (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀) := by
    dsimp [a, X]
    ring
  calc
    _ ≤ Real.exp (-a * X) := by rw [he0]; exact hbase
    _ ≤ Real.exp (-a * X / L) := hrate
    _ = _ := by rw [he]

end SupercriticalLQGUniqueness.B2.DG20Conc

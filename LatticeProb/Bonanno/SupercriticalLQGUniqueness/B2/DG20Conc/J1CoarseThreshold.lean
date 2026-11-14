/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseThreshold at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseParameter

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_coarse_parameter_inv_identity
    (ξ B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T) :
    Real.exp (|ξ| * B *
      Real.log (j1CoarseTailParameter ξ B T)) * T⁻¹ =
      (j1CoarseTailParameter ξ B T)⁻¹ := by
  have hs : 0 < j1CoarseTailParameter ξ B T :=
    j1_coarse_parameter_pos ξ B T hT
  have h := j1_coarse_parameter_identity ξ B T hB hT
  have hT0 : T ≠ 0 := hT.ne'
  have hs0 : j1CoarseTailParameter ξ B T ≠ 0 := hs.ne'
  field_simp [hT0, hs0]
  nlinarith

theorem j1_coarse_lower_threshold
    (ξ B T L : ℝ) (hB : 0 ≤ B) (hT : 0 < T) :
    ENNReal.ofReal (Real.exp (|ξ| * B *
        Real.log (j1CoarseTailParameter ξ B T))) *
      ENNReal.ofReal (T⁻¹ * L) =
      ENNReal.ofReal ((j1CoarseTailParameter ξ B T)⁻¹ * L) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [← mul_assoc, j1_coarse_parameter_inv_identity ξ B T hB hT]

theorem j1_coarse_upper_threshold
    (ξ B T L : ℝ) (hB : 0 ≤ B) (hT : 0 < T) :
    ENNReal.ofReal (Real.exp (|ξ| * B *
        Real.log (j1CoarseTailParameter ξ B T))) *
      ENNReal.ofReal (j1CoarseTailParameter ξ B T * L) =
      ENNReal.ofReal (T * L) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [← mul_assoc, j1_coarse_parameter_identity ξ B T hB hT]

end SupercriticalLQGUniqueness.B2.DG20Conc

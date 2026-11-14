/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseScaledThreshold at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseThreshold

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_coarse_scaled_lower_threshold
    (ξ B T r L : ℝ) (hB : 0 ≤ B) (hT : 0 < T)
    (hr : 0 ≤ r) :
    ENNReal.ofReal (Real.exp (|ξ| * B *
        Real.log (j1CoarseTailParameter ξ B T))) *
      ENNReal.ofReal (T⁻¹ * (r * L)) =
      ENNReal.ofReal r *
        ENNReal.ofReal ((j1CoarseTailParameter ξ B T)⁻¹ * L) := by
  rw [j1_coarse_lower_threshold ξ B T (r * L) hB hT,
    ← ENNReal.ofReal_mul hr]
  congr 1
  ring

theorem j1_coarse_scaled_upper_threshold
    (ξ B T r L : ℝ) (hB : 0 ≤ B) (hT : 0 < T)
    (hr : 0 ≤ r) :
    ENNReal.ofReal (Real.exp (|ξ| * B *
        Real.log (j1CoarseTailParameter ξ B T))) *
      ENNReal.ofReal (j1CoarseTailParameter ξ B T * (r * L)) =
      ENNReal.ofReal (T * (r * L)) := by
  exact j1_coarse_upper_threshold ξ B T (r * L) hB hT

end SupercriticalLQGUniqueness.B2.DG20Conc

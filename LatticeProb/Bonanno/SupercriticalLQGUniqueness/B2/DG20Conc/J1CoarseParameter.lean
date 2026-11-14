/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseParameter at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearRoundFullTransfer

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

def j1CoarseTailParameter (ξ B T : ℝ) : ℝ :=
  T ^ (1 / (1 + |ξ| * B))

theorem j1_coarse_parameter_log
    (ξ B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T) :
    Real.log (j1CoarseTailParameter ξ B T) =
      Real.log T / (1 + |ξ| * B) := by
  have hD : 0 < 1 + |ξ| * B := by positivity
  rw [j1CoarseTailParameter, Real.log_rpow hT]
  ring

theorem j1_coarse_parameter_pos
    (ξ B T : ℝ) (hT : 0 < T) :
    0 < j1CoarseTailParameter ξ B T := by
  unfold j1CoarseTailParameter
  positivity

theorem j1_coarse_parameter_identity
    (ξ B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T) :
    Real.exp (|ξ| * B *
      Real.log (j1CoarseTailParameter ξ B T)) *
      j1CoarseTailParameter ξ B T = T := by
  have hD : 0 < 1 + |ξ| * B := by positivity
  have hs : 0 < j1CoarseTailParameter ξ B T :=
    j1_coarse_parameter_pos ξ B T hT
  have hsEq : j1CoarseTailParameter ξ B T =
      Real.exp (Real.log T / (1 + |ξ| * B)) := by
    rw [j1CoarseTailParameter, Real.rpow_def_of_pos hT]
    congr 1
    ring
  rw [hsEq, Real.log_exp, ← Real.exp_add]
  have harg : |ξ| * B * (Real.log T / (1 + |ξ| * B)) +
      Real.log T / (1 + |ξ| * B) = Real.log T := by
    field_simp
    ring
  rw [harg, Real.exp_log hT]

end SupercriticalLQGUniqueness.B2.DG20Conc

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Threshold at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2CanonicalUpper

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA2_split_parameter {ξ T : ℝ} (hξ : 0 < ξ) (hT : 36 < T) :
    ∃ S M : ℝ, 6 < S ∧ 0 < M ∧ S ^ 2 = T ∧
      Real.log S = Real.log T / 2 ∧
      Real.exp (|ξ| * M) = S ∧ Real.exp (-(|ξ| * M)) = S⁻¹ := by
  let S := Real.exp (Real.log T / 2)
  let M := Real.log T / (2 * ξ)
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hM : 0 < M := div_pos hlog (by positivity)
  have hS0 : 0 < S := Real.exp_pos _
  have hSsq : S ^ 2 = T := by
    dsimp [S]
    calc
      Real.exp (Real.log T / 2) ^ 2 =
          Real.exp (Real.log T / 2 + Real.log T / 2) := by
            rw [sq, Real.exp_add]
      _ = Real.exp (Real.log T) := by congr 1; ring
      _ = T := Real.exp_log hT0
  have hS : 6 < S := by nlinarith [hSsq]
  have hlogS : Real.log S = Real.log T / 2 := Real.log_exp _
  have he : Real.exp (|ξ| * M) = S := by
    rw [abs_of_pos hξ]
    dsimp [M, S]
    congr 1
    field_simp
  refine ⟨S, M, hS, hM, hSsq, hlogS, he, ?_⟩
  rw [Real.exp_neg, he]

end SupercriticalLQGUniqueness.B2.DG20Conc

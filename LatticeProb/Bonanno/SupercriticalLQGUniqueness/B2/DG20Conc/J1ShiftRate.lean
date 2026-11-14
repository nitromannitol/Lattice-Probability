/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1ShiftRate at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1ThresholdShift
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ThresholdExp
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneAShift
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LargeSameP
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUnitGeometry

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_induction_parameter_large {A₀ C T : ℝ}
    (hA₀ : 0 < A₀) (hC : 0 ≤ C) (K : ℕ)
    (hT : Real.exp ((A₀ + 5) * (C + 1) *
      Real.sqrt ((K : ℝ) + 1)) ≤ T) :
    let B := Real.exp (C * Real.sqrt (K : ℝ))
    max (3 * B) (B^2) < T := by
  dsimp
  let x : ℝ := Real.sqrt ((K : ℝ) + 1)
  let y : ℝ := Real.sqrt (K : ℝ)
  have hx : 1 ≤ x := by
    dsimp [x]
    simpa using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ (K : ℝ) + 1 by positivity)
  have hyx : y ≤ x := by
    dsimp [x, y]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hDE : Real.exp (C * y) ≤ Real.exp (C * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hyx hC)
  have hcoef : 2 * C + 5 ≤ (A₀ + 5) * (C + 1) := by
    nlinarith
  have hT' : Real.exp ((2 * C + 5) * x) ≤ T :=
    (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hcoef (by linarith))).trans hT
  exact laneA2_max_shift_of_exp (Real.exp_nonneg _) hC hx hDE hT'

theorem j1_induction_shifted_rates {A₀ C cN cP CN CP T : ℝ}
    (hA₀ : 0 < A₀) (hC : 0 ≤ C)
    (hcN : 0 < cN) (hcP : 0 < cP)
    (hCN : 0 ≤ CN) (hCP : 0 ≤ CP)
    (K : ℕ)
    (hT : Real.exp ((A₀ + 5) * (C + 1) *
      Real.sqrt ((K : ℝ) + 1)) ≤ T) :
    let B := Real.exp (C * Real.sqrt (K : ℝ))
    CN * Real.exp (-cN * (Real.log (T / B))^2) ≤
      CN * Real.exp (-(cN / 4) * (Real.log T)^2) ∧
    CP * Real.exp (-cP * (Real.log (T / B))^2 /
        Real.log (Real.log (T / B))) ≤
      CP * Real.exp (-(cP / 4) * (Real.log T)^2 /
        Real.log (Real.log T)) := by
  dsimp
  let B : ℝ := Real.exp (C * Real.sqrt (K : ℝ))
  have hB : 1 ≤ B := Real.one_le_exp (mul_nonneg hC (Real.sqrt_nonneg _))
  have hbig := j1_induction_parameter_large hA₀ hC K hT
  constructor
  · exact laneA2_shifted_lower_tail_rate hB hbig hCN hcN
  · have hshift := laneA_shifted_log_rate hB hbig
    have hmul := mul_le_mul_of_nonneg_left hshift hcP.le
    have hexp : Real.exp (-cP * (Real.log (T / B))^2 /
        Real.log (Real.log (T / B))) ≤
        Real.exp (-(cP / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = -(cP * ((Real.log (T / B))^2 /
            Real.log (Real.log (T / B)))) := by ring
        _ ≤ -(cP * ((Real.log T)^2 /
            (4 * Real.log (Real.log T)))) := neg_le_neg hmul
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left hexp hCP

end SupercriticalLQGUniqueness.B2.DG20Conc

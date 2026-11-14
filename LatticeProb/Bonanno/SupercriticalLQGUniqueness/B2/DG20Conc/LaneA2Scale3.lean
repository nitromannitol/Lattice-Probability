/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Scale3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2DyadicSplit
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneA2_fine_scale_three
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W)
    {m : ℕ} (hm : 3 ≤ m) (a b : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | lenObs ξ (phiMN W P 3 m) (rectAB ((1 / 8) * a) ((1 / 8) * b)) ω ∈ S} =
      P {ω | (1 / 8 : ℝ) * lenObs ξ (phiMN W P 0 (m - 3)) (rectAB a b) ω ∈ S} := by
  have h := dddf_eq230 (ξ := ξ) hW ((1 / 8 : ℝ) * a) ((1 / 8 : ℝ) * b) hm hS
  have hA : (2 : ℝ) ^ 3 * ((1 / 8 : ℝ) * a) = a := by norm_num; ring
  have hB : (2 : ℝ) ^ 3 * ((1 / 8 : ℝ) * b) = b := by norm_num; ring
  simpa only [lenMN, hA, hB, show (2 : ℝ)⁻¹ ^ 3 = 1 / 8 by norm_num] using h

end SupercriticalLQGUniqueness.B2.DG20Conc

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLargeAnnulusOsc at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPhiOscGaussianEvent

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneB_large_radius_le_one {K m : ℕ} (hKm : m + 1 ≤ K) :
    2 * (2 : ℝ)⁻¹ ^ (K - m) ≤ 1 := by
  have hpow : (2 : ℝ)⁻¹ ^ (K - m) ≤ (2 : ℝ)⁻¹ ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at hpow
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleEventually at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Filter Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneC_eventually_two_le_K_pow {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → 2 ≤ (K : ℝ) ^ ε := by
  have hlim : Tendsto (fun K : ℕ => (K : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.1 (hlim.eventually_ge_atTop 2)

 


end SupercriticalLQGUniqueness.B2.DG20Conc

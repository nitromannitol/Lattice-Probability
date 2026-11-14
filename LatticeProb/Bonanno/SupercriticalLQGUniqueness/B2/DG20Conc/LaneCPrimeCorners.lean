/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeCorners at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeWide
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

theorem laneC_prime_wide_corners
    {top bot left right : ℝ → ℂ}
    (htop : AdmPath (laneCPrimeWideRect 0).toSet
      (laneCPrimeWideRect 0).side₁ (laneCPrimeWideRect 0).side₂ top)
    (hbot : AdmPath (laneCPrimeWideRect 1).toSet
      (laneCPrimeWideRect 1).side₁ (laneCPrimeWideRect 1).side₂ bot)
    (hleft : AdmPath (laneCPrimeWideRect 2).toSet
      (laneCPrimeWideRect 2).side₁ (laneCPrimeWideRect 2).side₂ left)
    (hright : AdmPath (laneCPrimeWideRect 3).toSet
      (laneCPrimeWideRect 3).side₁ (laneCPrimeWideRect 3).side₂ right) :
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, top s = left t) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, top s = right t) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, bot s = left t) ∧
    (∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, bot s = right t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply hv_meet (H := laneCPrimeWideRect 0) (V := laneCPrimeWideRect 2)
    all_goals first | assumption | norm_num [laneCPrimeWideRect]
  · apply hv_meet (H := laneCPrimeWideRect 0) (V := laneCPrimeWideRect 3)
    all_goals first | assumption | norm_num [laneCPrimeWideRect]
  · apply hv_meet (H := laneCPrimeWideRect 1) (V := laneCPrimeWideRect 2)
    all_goals first | assumption | norm_num [laneCPrimeWideRect]
  · apply hv_meet (H := laneCPrimeWideRect 1) (V := laneCPrimeWideRect 3)
    all_goals first | assumption | norm_num [laneCPrimeWideRect]

end SupercriticalLQGUniqueness.B2.DG20Conc

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBProbabilityTransfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLogThreshold

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 


theorem laneB_measure_le_of_ae_good_imp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B Bad : Set Ω)
    (h : ∀ᵐ ω ∂P, ω ∈ A → ω ∉ Bad → ω ∈ B) :
    P A ≤ P B + P Bad := by
  calc
    P A ≤ P (B ∪ Bad) := by
      apply measure_mono_ae
      filter_upwards [h] with ω hω hA
      by_cases hbad : ω ∈ Bad
      · exact Or.inr hbad
      · exact Or.inl (hω hA hbad)
    _ ≤ P B + P Bad := measure_union_le _ _

 



end SupercriticalLQGUniqueness.B2.DG20Conc

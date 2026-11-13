/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P9FullPathClosure at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsFullPath
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P9JointClosure

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

theorem dgff_jointComparison_of_fullPathComparison
    (hfull : Inputs.DGFFWhiteNoiseFullPathComparison) :
    Inputs.DGFFWhiteNoiseJointComparison := by
  intro ξ Ω _ P W hW
  obtain ⟨J, hJprob, hJD, hJP, hpath⟩ := hfull ξ P W hW
  refine ⟨J, hJprob, hJD, hJP, ?_⟩
  letI (n : ℕ) : IsProbabilityMeasure (J n) := hJprob n
  intro δ hδ
  apply Filter.Tendsto.squeeze' (hpath δ hδ) tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    apply measure_mono
    rintro v ⟨N, p, hs, ht, hp, hc⟩
    exact (dgffAnnulusDistance_le_fullPathCost_four n N p hn hs ht hp
      (ξ : ℝ) v.1).trans hc
  · filter_upwards [] with n
    exact prob_le_one

theorem dg20ExponentPositive_of_P5_fullPathComparison
    (hlower : Inputs.DGFFInductionLowerWindow)
    (hfull : Inputs.DGFFWhiteNoiseFullPathComparison) :
    Iface.DG20ExponentPositive :=
  dg20ExponentPositive_of_P5_jointComparison hlower
    (dgff_jointComparison_of_fullPathComparison hfull)

end SupercriticalLQGUniqueness.B2.QPos

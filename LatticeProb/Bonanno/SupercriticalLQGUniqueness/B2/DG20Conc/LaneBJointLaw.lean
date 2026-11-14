/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBJointLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.WhiteNoise

 

theorem laneB_map_whiteNoise_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (W : WNSpace → Ω → ℝ) (V : WNSpace → Ω' → ℝ)
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P' V) :
    P.map (fun ω f => W f ω) = P'.map (fun ω f => V f ω) := by
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  letI : IsProbabilityMeasure P' := hV.isProbabilityMeasure
  refine map_eq_of_forall_finset'
    (measurable_pi_iff.mpr hW.measurable).aemeasurable
    (measurable_pi_iff.mpr hV.measurable).aemeasurable fun I => ?_
  exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec (ι := I)
    (U := fun f => W f) (V := fun f => V f)
    (hW.isGaussianProcess.hasGaussianLaw I)
    (hV.isGaussianProcess.hasGaussianLaw I)
    (fun f => hW.measurable f) (fun f => hV.measurable f)
    (fun f => (hW.hasLaw_single f).hasGaussianLaw.memLp_two)
    (fun f => (hV.hasLaw_single f).hasGaussianLaw.memLp_two)
    (fun f => QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single f))
    (fun f => QuantumZipper.GFFExist.gs_integral_eq_zero (hV.hasLaw_single f))
    (fun f g => (hW.cov_eq f g).trans (hV.cov_eq f g).symm)

end SupercriticalLQGUniqueness.B2.DG20Conc

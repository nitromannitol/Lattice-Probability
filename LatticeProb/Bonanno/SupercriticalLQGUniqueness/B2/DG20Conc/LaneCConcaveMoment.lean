/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConcaveMoment at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelMean
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConditionalHolder

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_lintegral_rpow_le_rpow_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞} (hZ : Measurable Z)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫⁻ ω, Z ω ^ a ∂P) ≤ (∫⁻ ω, Z ω ∂P) ^ a := by
  have hconj : (1 / a).HolderConjugate (1 / (1 - a)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_div ha).2 (by linarith)
    · have ha' : a ≠ 0 := ha.ne'
      have hb' : 1 - a ≠ 0 := by linarith
      field_simp
      ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj
    (f := fun x => Z x ^ a) (g := fun _ => (1 : ℝ≥0∞))
    (hZ.pow_const a).aemeasurable measurable_const.aemeasurable
  have hpow (x : Ω) : (Z x ^ a) ^ (1 / a) = Z x := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ha.ne', ENNReal.rpow_one]
  have hq : 1 / (1 / a) = a := by field_simp
  have hq' : 1 / (1 / (1 - a)) = 1 - a := by
    have : 1 - a ≠ 0 := by linarith
    field_simp
  simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    measure_univ, ENNReal.coe_one, one_mul, hq, hq', hpow] using h

 

theorem laneC_conditional_lintegral_concave_moment
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {Z : Ω → ℝ≥0∞} (hZ : Measurable Z)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫⁻ ω, (∫⁻ x, Z x ∂(condExpKernel P m ω)) ^ a ∂P) ≤
      (∫⁻ x, Z x ∂P) ^ a := by
  have hM : Measurable (fun ω => ∫⁻ x, Z x ∂(condExpKernel P m ω)) :=
    (hZ.lintegral_kernel).mono hm le_rfl
  exact (laneC_lintegral_rpow_le_rpow_lintegral P hM ha ha1).trans
    (le_of_eq (congrArg (fun z : ℝ≥0∞ => z ^ a)
      (laneC_conditional_lintegral_mean P hm hZ)))

end SupercriticalLQGUniqueness.B2.DG20Conc

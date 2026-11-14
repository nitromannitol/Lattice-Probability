/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConditionalHolder at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.MeanInequalities

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_holder_conjugate (ζ : ℝ) (hζ : 0 < ζ) :
    ((1 + ζ) / ζ).HolderConjugate (1 + ζ) := by
  apply Real.holderConjugate_iff.mpr
  constructor
  · rw [one_lt_div hζ]
    linarith
  · have h1 : 0 < 1 + ζ := by linarith
    field_simp
    ring

 


theorem laneC_conditional_holder_at
    {Ω : Type*} [MeasurableSpace Ω] (κ : Measure Ω)
    {f g : Ω → ℝ≥0∞} (hf : AEMeasurable f κ) (hg : AEMeasurable g κ)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∫⁻ ω, f ω * g ω ∂κ ≤
      (∫⁻ ω, f ω ^ ((1 + ζ) / ζ) ∂κ) ^ (ζ / (1 + ζ)) *
        (∫⁻ ω, g ω ^ (1 + ζ) ∂κ) ^ (1 / (1 + ζ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq κ
    (laneC_holder_conjugate ζ hζ) hf hg
  have hq : 0 < 1 + ζ := by linarith
  have heq : 1 / ((1 + ζ) / ζ) = ζ / (1 + ζ) := by
    field_simp
  simpa only [heq, Pi.mul_apply] using h

end SupercriticalLQGUniqueness.B2.DG20Conc

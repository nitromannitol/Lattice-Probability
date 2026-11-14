/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelMean at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Kernel.Condexp

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_conditional_lintegral_mean
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {Z : Ω → ℝ≥0∞} (hZ : Measurable Z) :
    (∫⁻ ω, ∫⁻ x, Z x ∂(condExpKernel P m ω) ∂P) =
      ∫⁻ x, Z x ∂P := by
  let κ := condExpKernel P m
  have hmeas : Measurable[m] (fun ω => ∫⁻ x, Z x ∂(κ ω)) :=
    hZ.lintegral_kernel
  calc
    (∫⁻ ω, ∫⁻ x, Z x ∂(κ ω) ∂P) =
      ∫⁻ ω, ∫⁻ x, Z x ∂(κ ω) ∂(P.trim hm) :=
        (lintegral_trim hm hmeas).symm
    _ = ∫⁻ x, Z x ∂(κ ∘ₘ P.trim hm) := by
      exact (Measure.lintegral_bind (Kernel.aemeasurable κ) hZ.aemeasurable).symm
    _ = ∫⁻ x, Z x ∂P := by
      rw [show κ ∘ₘ P.trim hm = P from condExpKernel_comp_trim hm]

end SupercriticalLQGUniqueness.B2.DG20Conc

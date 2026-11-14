/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelAeMono at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.MeasurableIntegral

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_conditional_lintegral_mono_ae
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {f g : Ω → ℝ≥0∞}
    (hfg : f ≤ᵐ[P] g) :
    ∀ᵐ ω ∂P,
      (∫⁻ x, f x ∂(condExpKernel P m ω)) ≤
        ∫⁻ x, g x ∂(condExpKernel P m ω) := by
  have hcomp : f ≤ᵐ[(condExpKernel P m) ∘ₘ (P.trim hm)] g := by
    rw [condExpKernel_comp_trim hm]
    exact hfg
  have hkernel : ∀ᵐ ω ∂P.trim hm,
      f ≤ᵐ[condExpKernel P m ω] g :=
    Measure.ae_ae_of_ae_comp hcomp
  have hkernel' : ∀ᵐ ω ∂P,
      f ≤ᵐ[condExpKernel P m ω] g :=
    ae_of_ae_trim hm hkernel
  filter_upwards [hkernel'] with ω hω
  exact lintegral_mono_ae hω

end SupercriticalLQGUniqueness.B2.DG20Conc

import Mathlib

/-!
# Conditional independence of a family is stable under almost sure modification

If the variables `f i` are conditionally independent given a sub-σ-algebra and `g i` is almost
surely equal to `f i` for every `i`, then the variables `g i` are conditionally independent given
the same sub-σ-algebra (`iCondIndepFun.congr_ae`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {Ω ι : Type*} {m' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
  {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Conditional independence is insensitive to almost sure modification.** -/
theorem iCondIndepFun.congr_ae {β : ι → Type*} [mβ : ∀ i, MeasurableSpace (β i)]
    {f g : ∀ i, Ω → β i} (h : iCondIndepFun m' hm' f μ) (hfg : ∀ i, f i =ᵐ[μ] g i) :
    iCondIndepFun m' hm' g μ := by
  refine Kernel.iIndepFun.congr' h fun i => ?_
  have h1 : ∀ᵐ ω ∂(condExpKernel μ m' ∘ₘ μ.trim hm'), f i ω = g i ω := by
    rw [condExpKernel_comp_trim hm']
    exact hfg i
  exact Measure.ae_ae_of_ae_comp h1

end LatticeProb

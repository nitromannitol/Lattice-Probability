import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod

/-! # Independent resampling while preserving a mark -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LatticeProb

/-- Retain a measurable mark and independently sample a second coordinate. -/
def markResamplingKernel {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (f : α → β) (hf : Measurable f) (ν : Measure γ) :
    Kernel α (β × γ) :=
  (Kernel.deterministic f hf).prod (Kernel.const α ν)

instance {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (f : α → β) (hf : Measurable f) (ν : Measure γ)
    [IsProbabilityMeasure ν] : IsMarkovKernel (markResamplingKernel f hf ν) := by
  unfold markResamplingKernel
  infer_instance

/-- Resampling gives the product of the mark law and the resampling law. -/
theorem markResamplingKernel_comp {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α) [SFinite μ]
    (f : α → β) (hf : Measurable f) (ν : Measure γ) [SFinite ν] :
    markResamplingKernel f hf ν ∘ₘ μ = (μ.map f).prod ν := by
  have hk : markResamplingKernel f hf ν =
      ((Kernel.id : Kernel β β).prod (Kernel.const β ν)) ∘ₖ
        Kernel.deterministic f hf := by
    rw [Kernel.prod_const_comp]
    simp only [Kernel.id_comp, markResamplingKernel]
  rw [hk, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map hf,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

end LatticeProb

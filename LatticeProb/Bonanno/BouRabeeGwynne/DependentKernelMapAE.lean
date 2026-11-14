/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.DependentKernelMapAE at commit fdb5cad; the proof uses the corresponding theorem in LatticeProb. -/
import LatticeProb.Bonanno.BouRabeeGwynne.DependentKernelMap
import LatticeProb.Prob.DependentKernelMap

/-! A joint past-dependent map may intertwine transition rows almost surely;
the irrelevant invalid histories need not satisfy the row identity. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

lemma compProd_map_dependent_of_kernel_map_ae
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (η : Kernel C D) [IsSFiniteKernel η]
    (f : A → C) (g : A → B → D) (hf : Measurable f)
    (hg : Measurable (fun p : A × B => g p.1 p.2))
    (hmap : ∀ᵐ a ∂μ, (κ a).map (g a) = η (f a)) :
    (μ ⊗ₘ κ).map (fun p => (f p.1, g p.1 p.2)) = μ.map f ⊗ₘ η :=
  LatticeProb.compProd_map_dependent_of_kernel_map_ae μ κ η f g hf hg hmap

end BouRabeeGwynne

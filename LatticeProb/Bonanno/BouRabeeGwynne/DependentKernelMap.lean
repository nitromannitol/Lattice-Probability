/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.DependentKernelMap at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Joint maps whose future component depends measurably on the entire past. -/

open MeasureTheory ProbabilityTheory Set

namespace BouRabeeGwynne

lemma compProd_map_dependent_of_kernel_map
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (η : Kernel C D) [IsSFiniteKernel η]
    (f : A → C) (g : A → B → D) (hf : Measurable f)
    (hg : Measurable (fun p : A × B => g p.1 p.2))
    (hmap : ∀ a, (κ a).map (g a) = η (f a)) :
    (μ ⊗ₘ κ).map (fun p => (f p.1, g p.1 p.2)) = μ.map f ⊗ₘ η := by
  have hp : Measurable (fun p : A × B => (f p.1, g p.1 p.2)) :=
    (hf.comp measurable_fst).prodMk hg
  ext s hs
  rw [Measure.map_apply hp hs, Measure.compProd_apply (hp hs),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro a
  have hga : Measurable (g a) := hg.comp (measurable_const.prodMk measurable_id)
  rw [← hmap a, Measure.map_apply hga (measurable_prodMk_left hs)]
  rfl

end BouRabeeGwynne

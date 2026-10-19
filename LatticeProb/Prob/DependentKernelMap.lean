/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/DependentKernelMap.lean and BouRabeeGwynne/DependentKernelMapAE.lean.
-/
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Pushforwards of composition products along dependent maps

Let `μ` be a measure on `A` and `κ : Kernel A B` a kernel.  If `g : A → B → D` pushes each
row `κ a` forward to `η (f a)`, then the image of `μ ⊗ₘ κ` under `p ↦ (f p.1, g p.1 p.2)` is
`μ.map f ⊗ₘ η`.  The almost-everywhere variant asks for the row identity only `μ`-almost
everywhere.
-/

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb

/-- If `g a` pushes the kernel row `κ a` forward to `η (f a)` for every `a`, and `f` and the
joint map `(a, b) ↦ g a b` are measurable, then the image of `μ ⊗ₘ κ` under
`p ↦ (f p.1, g p.1 p.2)` is `μ.map f ⊗ₘ η`. -/
theorem compProd_map_dependent_of_kernel_map
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

/-- The almost-everywhere variant of `LatticeProb.compProd_map_dependent_of_kernel_map`: the row
identity is only required for `μ`-almost every `a`, and the conclusion is the same. -/
theorem compProd_map_dependent_of_kernel_map_ae
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) [SFinite μ] (κ : Kernel A B) [IsSFiniteKernel κ]
    (η : Kernel C D) [IsSFiniteKernel η]
    (f : A → C) (g : A → B → D) (hf : Measurable f)
    (hg : Measurable (fun p : A × B => g p.1 p.2))
    (hmap : ∀ᵐ a ∂μ, (κ a).map (g a) = η (f a)) :
    (μ ⊗ₘ κ).map (fun p => (f p.1, g p.1 p.2)) = μ.map f ⊗ₘ η := by
  have hp : Measurable (fun p : A × B => (f p.1, g p.1 p.2)) :=
    (hf.comp measurable_fst).prodMk hg
  ext s hs
  rw [Measure.map_apply hp hs, Measure.compProd_apply (hp hs),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr_ae
  filter_upwards [hmap] with a ha
  have hga : Measurable (g a) := hg.comp (measurable_const.prodMk measurable_id)
  rw [← ha, Measure.map_apply hga (measurable_prodMk_left hs)]
  rfl

/-! Nonvacuity examples on `Bool`. -/

/-- Nonvacuity for `compProd_map_dependent_of_kernel_map`: `μ` is the Dirac mass at `true`,
`κ a` is the Dirac mass at `a` (a non-constant Markov kernel), `f = id`, `g a b = a && b`, and
`η x` is the Dirac mass at `x`. The row identity `dirac (a && a) = dirac a` holds for every `a`. -/
example :
    (Measure.dirac true ⊗ₘ Kernel.deterministic (fun x : Bool => x) measurable_id).map
        (fun p : Bool × Bool => ((fun x : Bool => x) p.1, p.1 && p.2)) =
      (Measure.dirac true).map (fun x : Bool => x) ⊗ₘ
        Kernel.deterministic (fun x : Bool => x) measurable_id :=
  compProd_map_dependent_of_kernel_map (Measure.dirac true)
    (Kernel.deterministic (fun x : Bool => x) measurable_id)
    (Kernel.deterministic (fun x : Bool => x) measurable_id)
    (fun x : Bool => x) (fun a b => a && b) measurable_id (measurable_of_countable _)
    (fun a => by
      rw [Kernel.deterministic_apply, Measure.map_dirac' (measurable_of_countable _)]
      cases a <;> rfl)

/-- Nonvacuity for `compProd_map_dependent_of_kernel_map_ae`: with `μ`, `κ`, and `η` as above,
`f = id`, and the constant map `g a b = true`, the row identity `dirac true = dirac a` holds
exactly at `a = true`. Since `μ` is the Dirac mass at `true`, it holds `μ`-almost everywhere,
even though it fails at `a = false`. -/
example :
    (Measure.dirac true ⊗ₘ Kernel.deterministic (fun x : Bool => x) measurable_id).map
        (fun p : Bool × Bool => ((fun x : Bool => x) p.1, true)) =
      (Measure.dirac true).map (fun x : Bool => x) ⊗ₘ
        Kernel.deterministic (fun x : Bool => x) measurable_id :=
  compProd_map_dependent_of_kernel_map_ae (Measure.dirac true)
    (Kernel.deterministic (fun x : Bool => x) measurable_id)
    (Kernel.deterministic (fun x : Bool => x) measurable_id)
    (fun x : Bool => x) (fun _ _ => true) measurable_id (measurable_of_countable _)
    (by
      refine (ae_dirac_iff ?_).2 ?_
      · exact (Set.toFinite _).measurableSet
      · rw [Kernel.deterministic_apply, Measure.map_dirac' (measurable_of_countable _)])

end LatticeProb

import LatticeProb.Prob.CellConfigLabelPathKernel

/-! # Configuration invariance for labelled cell walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- The augmented chain remains in every measurable configuration set containing
its starting configuration, simultaneously at all times. -/
theorem environmentChain_ae_mem (H : GMSSpace) (n : ℕ)
    {B : Set GMSSpace} (hB : MeasurableSet B) (hH : H ∈ B) :
    ∀ᵐ p ∂ReflectedWalk.MarkovChain.chainLaw environmentStep (H, n),
      ∀ j, (p j).1 ∈ B := by
  refine ReflectedWalk.MarkovChain.chainLaw_ae_forall_mem environmentStep
    (B := Prod.fst ⁻¹' B) (measurable_fst hB) ?_ hH
  intro y hy
  rw [environmentStep, Kernel.deterministic_prod_apply' measurable_fst kernel _
    ((measurable_fst hB).compl)]
  have hempty : (fun z : ℕ => (y.1, z)) ⁻¹'
      ((fun z : GMSSpace × ℕ => z.1) ⁻¹' B)ᶜ = ∅ := by
    ext z
    change (¬ y.1 ∈ B) ↔ False
    exact ⟨fun hn => hn hy, False.elim⟩
  rw [hempty, measure_empty]

/-- If the initial configuration is measurable as a singleton, the augmented
chain preserves it at every time almost surely. -/
theorem environmentChain_ae_eq (H : GMSSpace) (n : ℕ)
    (hH : MeasurableSet ({H} : Set GMSSpace)) :
    ∀ᵐ p ∂ReflectedWalk.MarkovChain.chainLaw environmentStep (H, n),
      ∀ j, (p j).1 = H := by
  simpa only [Set.mem_singleton_iff] using
    environmentChain_ae_mem H n hH (Set.mem_singleton H)

end LatticeProb.CellConfigLabelTransition

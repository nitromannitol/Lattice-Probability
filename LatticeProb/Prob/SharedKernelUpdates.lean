import Mathlib.Probability.Kernel.Representation

/-!
# Common updates for Markov kernels

Two Markov kernels that agree on a measurable set can be represented using the
same uniform noise by update functions that agree pointwise on that set.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Function unitInterval

namespace LatticeProb

/-- Markov kernels that agree on a measurable set admit common uniform updates there. -/
theorem exists_shared_kernel_updates {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (D : Set X) (hD : MeasurableSet D) (h : ∀ x ∈ D, κ x = η x) :
    ∃ F G : X → I → Y, Measurable (uncurry F) ∧ Measurable (uncurry G) ∧
      (∀ x, volume.map (F x) = κ x) ∧ (∀ x, volume.map (G x) = η x) ∧
      ∀ x ∈ D, ∀ u, F x u = G x u := by
  classical
  obtain ⟨F, hF, hFκ⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  obtain ⟨H, hH, hHη⟩ := Kernel.exists_measurable_map_eq_unitInterval η
  refine ⟨F, fun x u => if x ∈ D then F x u else H x u, hF, ?_, hFκ, ?_, ?_⟩
  · exact Measurable.ite (hD.preimage measurable_fst) hF hH
  · intro x
    by_cases hx : x ∈ D
    · simpa only [ite_eq_left hx] using (hFκ x).trans (h x hx)
    · simpa only [ite_eq_right hx] using hHη x
  · intro x hx u
    simp only [ite_eq_left hx]

end LatticeProb

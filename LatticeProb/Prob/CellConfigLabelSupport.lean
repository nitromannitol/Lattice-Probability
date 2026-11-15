import LatticeProb.Prob.CellConfigLabelFibre

/-! # Support of labelled cell walks -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- An occupied label cannot jump to an unoccupied label, including in a zero row. -/
theorem step_eq_zero_of_occupied_of_absent (H : GMSSpace) {n m : ℕ}
    (hn : H.1.slot n ≠ none) (hm : H.1.slot m = none) :
    step H n m = 0 := by
  have hne : m ≠ n := by
    intro h
    subst m
    exact hn hm
  by_cases hrow : rowTotal H n = 0
  · simp [step, hrow, hne]
  · simp [step, hrow, CellConfig.codeCond_of_none_right hm]

/-- A labelled walk started at an occupied label stays on occupied labels almost surely. -/
theorem pathKernel_ae_occupied (H : GMSSpace) {n : ℕ} (hn : H.1.slot n ≠ none) :
    ∀ᵐ p ∂pathKernel (H, n), ∀ j, H.1.slot (p j) ≠ none := by
  rw [pathKernel_eq_fixedChain]
  apply ReflectedWalk.MarkovChain.chainLaw_ae_forall_mem (fixedKernel H)
    (B := {m | H.1.slot m ≠ none}) (MeasurableSet.of_discrete) ?_ hn
  intro a ha
  refine measure_mono_null (t := ⋃ m : ℕ, if H.1.slot m = none then {m} else ∅) ?_
    (measure_iUnion_null fun m => ?_)
  · intro m hm
    have hm : H.1.slot m = none := by simpa only [mem_compl_iff, mem_ofPred_eq, not_not] using hm
    exact mem_iUnion.mpr ⟨m, by simp [hm]⟩
  · by_cases hm : H.1.slot m = none
    · simp only [hm, ↓reduceIte, fixedKernel, Kernel.comap_apply, kernel_singleton,
        step_eq_zero_of_occupied_of_absent H ha hm, ENNReal.ofReal_zero]
    · simp [hm]

end LatticeProb.CellConfigLabelTransition

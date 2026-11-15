import LatticeProb.Walk.CellConfigSRWChain
import LatticeProb.Prob.CellConfigWalkMeasurable

/-! # Paths of the recurrent cell walk -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open ReflectedGMS.GMS MatedCRTHarmonic.Markov

namespace LatticeProb.CellConfigWalk

/-- On a valid configuration without isolated cells, every jump of a simple
random walk follows a positive-conductance edge almost surely. -/
theorem ae_adjacent_of_isSRWLaw (H : CellConfig) (hH : H.IsCellConfiguration)
    (hne : ∀ K : H.cells, ∃ K' : H.cells, H.Adj K K')
    {K : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K Q) :
    ∀ᵐ ω ∂Q, ∀ n, H.Adj (ω n) (ω (n + 1)) := by
  classical
  let : Countable H.cells := countable_cells_of_locallyFinite hH.locallyFinite
  let : IsMarkovKernel (CellConfigSRW.kernel H) := CellConfigSRW.isMarkovKernel_kernel H hH
  rw [CellConfigSRW.eq_walkLaw_of_isSRWLaw H hH hQ]
  apply MatedCRTHarmonic.Harmonic.ae_forall_succ_mem (CellConfigSRW.kernel H) K
    (fun x => {y | H.Adj x y})
  intro x
  have hpi : 0 < H.pi x := (hne x).elim fun _ h => pi_pos_of_adj hH h
  have hz : ∀ y : H.cells, ¬ H.Adj x y → CellConfigSRW.kernel H x {y} = 0 := by
    intro y hy
    have hc : H.c x y = 0 := le_antisymm (not_lt.mp hy) (hH.c_nonneg _ _)
    rw [CellConfigSRW.kernel_singleton H hpi y]
    simp [CellConfig.transition, hc]
  refine measure_mono_null (t := ⋃ y : H.cells, if H.Adj x y then ∅ else {y}) ?_
    (measure_iUnion_null fun y => ?_)
  · intro y hy
    change ¬ H.Adj x y at hy
    exact mem_iUnion.mpr ⟨y, by simp [hy]⟩
  · by_cases hy : H.Adj x y
    · simp [hy]
    · simpa [hy] using hz y hy

/-- Recurrence also makes the holding-time clock diverge almost surely. -/
theorem ae_valid_paths_of_recurrent (H : CellConfig) (hH : H.IsCellConfiguration)
    (hne : ∀ K : H.cells, ∃ K' : H.cells, H.Adj K K') (hrec : H.Recurrent)
    {K : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K Q) :
    ∀ᵐ ω ∂Q, H.JumpTimesUnbounded ω ∧ ∀ n, H.Adj (ω n) (ω (n + 1)) := by
  exact (ae_jumpTimesUnbounded_of_recurrent hrec
    (holding_pos_of_forall_exists_adj hH hne) hQ).and (ae_adjacent_of_isSRWLaw H hH hne hQ)

end LatticeProb.CellConfigWalk
end

import LatticeProb.Walk.CellConfigSRWChain

/-!
# Restarting a cell walk at its first hit

The future of a simple random walk after hitting a set of cells is a mixture of
fresh walk laws, with the first-hit distribution as mixing measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ReflectedGMS.GMS MatedCRTHarmonic.Markov

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig) [Countable H.cells]

/-- On the event of a finite hit, the shifted walk has the continuation law
obtained by mixing fresh walks over the first-hit cell. -/
theorem restrict_map_stopShift_hit (hH : H.IsCellConfiguration) (I : Set H.cells) {x : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw x Q) :
    (Q.restrict {ω | hitTime I ω < ⊤}).map (stopShift (hitTime I)) =
      @pathKernel H.cells _ (kernel H) (isMarkovKernel_kernel H hH) ∘ₘ
        (Q.restrict {ω | hitTime I ω < ⊤}).map (stopState (hitTime I)) := by
  have := isMarkovKernel_kernel H hH
  rw [eq_walkLaw_of_isSRWLaw H hH hQ]
  have h := restrict_map_stopShift (kernel H) x
    (isStoppingTime_hitTime (MeasurableSet.of_discrete : MeasurableSet I))
    (F := Set.univ) MeasurableSet.univ
  simpa only [Set.univ_inter, walkLaw] using h

/-- If the target is hit almost surely, no restriction is needed in the
first-hit continuation law. -/
theorem map_stopShift_hit (hH : H.IsCellConfiguration) (I : Set H.cells) {x : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw x Q)
    (hfin : ∀ᵐ ω ∂Q, hitTime I ω < ⊤) :
    Q.map (stopShift (hitTime I)) =
      @pathKernel H.cells _ (kernel H) (isMarkovKernel_kernel H hH) ∘ₘ Q.map (stopState (hitTime I)) := by
  have hr : Q.restrict {ω | hitTime I ω < ⊤} = Q :=
    Measure.restrict_eq_self_of_ae_mem hfin
  have h := restrict_map_stopShift_hit H hH I hQ
  rw [hr] at h
  exact h

end LatticeProb.CellConfigSRW

end

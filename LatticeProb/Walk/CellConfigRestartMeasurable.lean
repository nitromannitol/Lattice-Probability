import LatticeProb.Walk.CellConfigHittingRestart
import LatticeProb.Prob.CellConfigWalkExitMeasurable

/-!
# Measurability after restarting a cell walk

A first-hit continuation law is a countable mixture of fresh walk laws. An
observable that is almost everywhere measurable for each fresh walk is
therefore almost everywhere measurable for the continuation law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open ReflectedGMS ReflectedGMS.GMS MatedCRTHarmonic.Markov

namespace LatticeProb.CellConfigSRW

variable (H : CellConfig) [Countable H.cells]

/-- Almost everywhere measurability is preserved by a first-hit continuation. -/
theorem aemeasurable_stopShift_hit (hH : H.IsCellConfiguration) (I : Set H.cells)
    {x : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw x Q)
    (hfin : ∀ᵐ ω ∂Q, hitTime I ω < ⊤) {T : Type*} [MeasurableSpace T]
    (f : (ℕ → H.cells) → T) (hf : ∀ k, AEMeasurable f (walkLaw H hH k)) :
    AEMeasurable f (Q.map (stopShift (hitTime I))) := by
  let := isMarkovKernel_kernel H hH
  rw [map_stopShift_hit H hH I hQ hfin, Measure.comp_eq_sum_of_countable]
  apply AEMeasurable.sum_measure
  intro k
  simpa only [pathKernel_apply, walkLaw] using
    (hf k).smul_measure ((Q.map (stopState (hitTime I))) {k})

/-- On a recurrent configuration, a restarted interpolated walk is almost everywhere measurable. -/
theorem aemeasurable_interpolatedWalk_stopShift_hit (hH : H.IsCellConfiguration)
    (hadj : ∀ k : H.cells, ∃ k' : H.cells, H.Adj k k') (hrec : H.Recurrent)
    (I : Set H.cells) {x : H.cells} {Q : Measure (ℕ → H.cells)}
    (hQ : H.IsSRWLaw x Q) (hfin : ∀ᵐ ω ∂Q, hitTime I ω < ⊤)
    (p : H.cells → Plane) (ε : ℝ≥0) :
    AEMeasurable (H.interpolatedWalk p ε) (Q.map (stopShift (hitTime I))) := by
  apply aemeasurable_stopShift_hit H hH I hQ hfin
  intro k
  have hpi : 0 < H.pi k := (hadj k).elim fun _ hk =>
    CellConfigWalk.pi_pos_of_adj hH hk
  exact CellConfigWalk.aemeasurable_interpolatedWalk_of_recurrent hrec
    (CellConfigWalk.holding_pos_of_forall_exists_adj hH hadj)
    (isSRWLaw_walkLaw H hH hpi) p ε

/-- The exit position of a restarted interpolated walk is almost everywhere measurable. -/
theorem aemeasurable_exitPosition_stopShift_hit (hH : H.IsCellConfiguration)
    (hadj : ∀ k : H.cells, ∃ k' : H.cells, H.Adj k k') (hrec : H.Recurrent)
    (I : Set H.cells) {x : H.cells} {Q : Measure (ℕ → H.cells)}
    (hQ : H.IsSRWLaw x Q) (hfin : ∀ᵐ ω ∂Q, hitTime I ω < ⊤)
    (p : H.cells → Plane) (ε : ℝ≥0) {U : Set Plane} (hU : IsOpen U) :
    AEMeasurable (fun ω => (H.interpolatedWalk p ε ω)
      (LatticeProb.continuousExitTime U 0 (H.interpolatedWalk p ε ω)).toNNReal)
      (Q.map (stopShift (hitTime I))) :=
  (LatticeProb.measurable_continuousExitPosition hU).comp_aemeasurable
    (aemeasurable_interpolatedWalk_stopShift_hit H hH hadj hrec I hQ hfin p ε)

end LatticeProb.CellConfigSRW
end

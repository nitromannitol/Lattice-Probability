import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedSkeleton
import LatticeProb.Prob.SelectorOuterRestriction

/-! # Physical first-exit reconstruction for restricted selectors -/

set_option autoImplicit false

open Set
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

/-- A finite stopped skeleton with a selector active on the open domain
reconstructs the original curve stopped at its first exit. -/
theorem brownianSkeleton_restricted_stopped_concatenate
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (W : J → Set (Euc d)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) {U : Set (Euc d)} (hU : IsOpen U)
    (hactive : ∀ k x, x ∈ U → selector k x ≠ none)
    (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock W z j₀
      (fun k => LatticeProb.restrictSelector U (selector k)) n ω).2 ≠ ∞)
    (hstop : (brownianSkeletonClock W z j₀
      (fun k => LatticeProb.restrictSelector U (selector k)) n ω).1 = true)
    (P : TimePartition n) :
    unitCurveExitProjection U (P.concatenate (ExcursionTrajectory.prefixChain n d
      (fun k => (brownianSkeletonExcursion W z j₀
        (fun k => LatticeProb.restrictSelector U (selector k)) k ω).2))) =
      stoppedBrownianCurve U z ω := by
  let restricted := fun k => LatticeProb.restrictSelector U (selector k)
  have hnone : ∀ k x, restricted k x = none → x ∉ U := by
    intro k x h
    exact LatticeProb.restrictSelector_none_not_mem U (selector k) (hactive k) h
  exact brownianSkeleton_stopped_concatenate W z j₀ restricted n ω hfinite hU
    (brownianSkeletonClock_exit_le_of_stopped W z j₀ restricted hnone n ω hfinite hstop) P

end BouRabeeGwynne

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppedSkeleton at commit fdb5cad; selected declaration; local import path and deprecated lemma name are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianSkeletonPrefix

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval NNReal ENNReal

namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem brownianSkeletonClock_exit_le_of_stopped (W : J → Set (Euc d))
    (z : Euc d) (j₀ : J) (selector : ℕ → Euc d → Option J)
    {U : Set (Euc d)} (hnone : ∀ n x, selector n x = none → x ∉ U)
    (n : ℕ) (ω : BrownianPath d)
    (hfinite : (brownianSkeletonClock W z j₀ selector n ω).2 ≠ ∞)
    (hstop : (brownianSkeletonClock W z j₀ selector n ω).1 = true) :
    continuousExitTime U z ω ≤ (brownianSkeletonClock W z j₀ selector n ω).2 := by
  induction n with
  | zero => cases hstop
  | succ n ih =>
    have hfprev := brownianSkeletonClock_finite_of_le W z j₀ selector ω (Nat.le_succ n) hfinite
    by_cases hp : (brownianSkeletonClock W z j₀ selector n ω).1 = true
    · exact (ih hfprev hp).trans (brownianSkeletonClock_time_le_succ W z j₀ selector n ω)
    · have hc : brownianClockChoice z (selector (n + 1))
          (brownianSkeletonClock W z j₀ selector n) ω = none := by
        change (brownianClockChoice z (selector (n + 1))
          (brownianSkeletonClock W z j₀ selector n) ω).isNone = true at hstop
        cases he : brownianClockChoice z (selector (n + 1))
            (brownianSkeletonClock W z j₀ selector n) ω with
        | none => rfl
        | some j => simp only [he, Option.isNone_some] at hstop; cases hstop
      have hsel : selector (n + 1)
          (z + ω (brownianSkeletonClock W z j₀ selector n ω).2.toNNReal) = none := by
        simpa only [brownianClockChoice, ite_eq_right hp] using hc
      have he := continuousExitTime_le_of_not_mem (hnone (n + 1) _ hsel)
      rw [ENNReal.coe_toNNReal hfprev] at he
      exact he.trans (brownianSkeletonClock_time_le_succ W z j₀ selector n ω)


end BouRabeeGwynne

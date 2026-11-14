/- The active-step argument adapts Leonardo Bonanno, BouRabeeGwynne.BrownianActiveSkeletonTail,
   https://github.com/leobon12/lean-formalizations, commit fdb5cad. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianActiveSkeletonTail

/-!
# Active successive exit clocks

An active step selects an exit domain and, if finite, its endpoint lies outside that domain.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
/-- An active finite clock step selects a domain at its starting point and ends outside it. -/
theorem brownianSkeletonClock_active_step_exit (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) (n : ℕ) (ω : BrownianPath d)
    (hactive : (brownianSkeletonClock U z j₀ selector (n + 1) ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector (n + 1) ω).2 ≠ ∞) :
    ∃ j, selector (n + 1) (z + ω (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal) = some j ∧
      z + ω (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal ∉ U j := by
  let τ : BrownianPath d → ℝ≥0∞ := fun η ↦ (brownianSkeletonClock U z j₀ selector n η).2
  have hex : ∃ j, brownianClockChoice z (selector (n + 1))
      (brownianSkeletonClock U z j₀ selector n) ω = some j := by
    change (brownianClockChoice z (selector (n + 1))
      (brownianSkeletonClock U z j₀ selector n) ω).isNone = false at hactive
    cases hc : brownianClockChoice z (selector (n + 1))
        (brownianSkeletonClock U z j₀ selector n) ω with
    | none => simp only [hc, Option.isNone_none] at hactive; cases hactive
    | some j => exact ⟨j, rfl⟩
  obtain ⟨j, hc⟩ := hex
  have hselect : selector (n + 1) (z + ω (τ ω).toNNReal) = some j := by
    by_cases hf : (brownianSkeletonClock U z j₀ selector n ω).1 = true
    · simp only [brownianClockChoice, hf, ↓reduceIte] at hc
      cases hc
    · simpa only [brownianClockChoice, hf, Bool.false_eq_true, ↓reduceIte] using hc
  have hnext : (brownianSkeletonClock U z j₀ selector (n + 1) ω).2 =
      brownianNextExitTime (U j) z τ ω := by
    change brownianSelectedNextExitTime U z τ
      (brownianClockChoice z (selector (n + 1)) (brownianSkeletonClock U z j₀ selector n)) ω = _
    simp only [brownianSelectedNextExitTime, hc]
  have hnf : brownianNextExitTime (U j) z τ ω ≠ ∞ := hnext ▸ hfinite
  have hη := (ENNReal.add_ne_top.mp hnf).2
  have hout := continuousExitTime_not_mem (hU j) hη
  have hend := stoppedBrownianRepresentative_next_endPoint (U j) z τ ω hnf
  rw [stoppedBrownianRepresentative_endPoint, ← hnext] at hend
  rw [hend] at hout
  exact ⟨j, hselect, hout⟩

end BouRabeeGwynne

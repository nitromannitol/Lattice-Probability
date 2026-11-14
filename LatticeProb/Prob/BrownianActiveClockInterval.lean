import LatticeProb.Bonanno.BouRabeeGwynne.BrownianActiveSkeletonTail
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitInterval
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel

/-!
# Confinement between successive exit clocks

An active finite step stays in the closure of its selected domain until its exit.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

variable {d : ℕ} {J : Type*} [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

omit [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)] in
/-- The selected excursion, including its terminal point, stays in the domain closure. -/
theorem brownianSkeletonClock_active_step_interval (U : J → Set (Euc d))
    (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J)
    (hstart : ∀ n x j, selector n x = some j → x ∈ U j)
    (n : ℕ) (ω : BrownianPath d)
    (hactive : (brownianSkeletonClock U z j₀ selector (n + 1) ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector (n + 1) ω).2 ≠ ∞) :
    ∃ j, selector (n + 1) (z + ω (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal) = some j ∧
      ∀ t ∈ Icc (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal
          (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal,
        z + ω t ∈ closure (U j) := by
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
  have hshift : (z + ω (τ ω).toNNReal) +
      shiftedBrownianPath (τ ω).toNNReal ω 0 ∈ U j := by
    simpa only [shiftedBrownianPath, ContinuousMap.coe_mk, add_zero, sub_self] using
      hstart (n + 1) (z + ω (τ ω).toNNReal) j hselect
  refine ⟨j, hselect, ?_⟩
  intro t ht
  have ht' : t ∈ Icc (τ ω).toNNReal (brownianNextExitTime (U j) z τ ω).toNNReal := by
    simpa only [← hnext] using ht
  obtain ⟨u, hu⟩ := mem_range_stoppedBrownianNextRepresentative (U j) z τ ω hnf ht'
  exact hu ▸ stoppedBrownianRepresentative_mem_closure (hU j) hshift
    (ENNReal.add_ne_top.mp hnf).2 u

end BouRabeeGwynne

import LatticeProb.Prob.BrownianActiveClockStrict
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRestart

/-!
# Strict initial Brownian excursion clocks

Prepending time zero to a finite active skeleton gives a strictly increasing
sequence of excursion times, including the first excursion.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- The initial excursion and each later active excursion take positive time. -/
theorem brownianSkeletonClock_prepend_zero_lt_succ {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) {ε : ℝ} (hε : 0 < ε)
    (hmargin : ∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j)
    (K : ℕ) (ω : BrownianPath d) (hstart : z + ω 0 ∈ U j₀)
    (hactive : (brownianSkeletonClock U z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector K ω).2 ≠ ∞)
    (n : ℕ) (hn : n < K + 1) :
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ selector m ω).2.toNNReal)
    T n < T (n + 1) := by
  cases n with
  | zero =>
    have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω (Nat.zero_le K) hfinite
    have hp := continuousExitTime_pos_of_mem (hU j₀) hstart
    change 0 < (brownianSkeletonClock U z j₀ selector 0 ω).2.toNNReal
    exact ENNReal.toNNReal_pos hp.ne' hf
  | succ n =>
    have hn' : n < K := by omega
    simpa only [Nat.succ_eq_add_one] using
      brownianSkeletonClock_active_time_lt_succ U hU z j₀ selector hε hmargin
        K ω hactive hfinite n hn'

/-- Clipping the prepended times preserves strictness before any cutoff. -/
theorem brownianSkeletonClock_prepend_zero_clipped_lt_succ {d : ℕ} {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) {ε : ℝ} (hε : 0 < ε)
    (hmargin : ∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j)
    (K : ℕ) (ω : BrownianPath d) (hstart : z + ω 0 ∈ U j₀)
    (hactive : (brownianSkeletonClock U z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector K ω).2 ≠ ∞)
    (a : ℝ≥0) (n : ℕ) (hn : n < K + 1) :
    let T : ℕ → ℝ≥0 := fun k => Nat.casesOn k 0
      (fun m => (brownianSkeletonClock U z j₀ selector m ω).2.toNNReal)
    T n < a → min (T n) a < min (T (n + 1)) a := by
  dsimp only
  intro hbefore
  rw [min_eq_left hbefore.le]
  exact lt_min (brownianSkeletonClock_prepend_zero_lt_succ U hU z j₀ selector hε hmargin
    K ω hstart hactive hfinite n hn) hbefore

end BouRabeeGwynne

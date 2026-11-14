import LatticeProb.Bonanno.BouRabeeGwynne.BrownianActiveSkeletonTail

/-!
# Strict active Brownian skeleton clocks

Positive-margin active excursions have strictly increasing finite clock times.
Clipping the times at a cutoff preserves strictness before the cutoff.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Successive finite active excursions with a positive margin take positive time. -/
theorem brownianSkeletonClock_active_time_lt_succ {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) {ε : ℝ} (hε : 0 < ε)
    (hmargin : ∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j)
    (K : ℕ) (ω : BrownianPath d)
    (hactive : (brownianSkeletonClock U z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector K ω).2 ≠ ∞)
    (n : ℕ) (hn : n < K) :
    (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal <
      (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal := by
  have hnK : n + 1 ≤ K := Nat.succ_le_of_lt hn
  have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω hnK hfinite
  have ha := brownianSkeletonClock_active_of_le U z j₀ selector ω hnK hactive
  have hdist := brownianSkeletonClock_active_step_dist U hU z j₀ selector hmargin n ω ha hf
  have hle : (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal ≤
      (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal :=
    ENNReal.toNNReal_mono hf (brownianSkeletonClock_time_le_succ U z j₀ selector n ω)
  apply lt_of_le_of_ne hle
  intro heq
  rw [heq, dist_self] at hdist
  exact (not_le_of_gt hε) hdist

/-- Clipping a finite active skeleton at a cutoff preserves strict increase until the cutoff. -/
theorem brownianSkeletonClock_active_clipped_time_lt_succ {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) {ε : ℝ} (hε : 0 < ε)
    (hmargin : ∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j)
    (K : ℕ) (ω : BrownianPath d)
    (hactive : (brownianSkeletonClock U z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector K ω).2 ≠ ∞)
    (T : ℝ≥0) (n : ℕ) (hn : n < K)
    (hbefore : (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal < T) :
    min (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal T <
      min (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal T := by
  rw [min_eq_left hbefore.le]
  exact lt_min (brownianSkeletonClock_active_time_lt_succ U hU z j₀ selector hε hmargin
    K ω hactive hfinite n hn) hbefore

end BouRabeeGwynne

import LatticeProb.Prob.BrownianActiveClockExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitRestart

/-!
# Strict clocks for excursions from open domains

Finite active excursions take positive time when each selected domain contains
its starting point. The same holds for the sequence with zero prepended and
for its truncation before a fixed cutoff.
-/

set_option autoImplicit false

open Set
open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- Finite active excursions from their selected open domains take positive time. -/
theorem brownianSkeletonClock_active_time_lt_succ_of_mem {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J)
    (hstart : ∀ n x j, selector n x = some j → x ∈ U j)
    (K : ℕ) (ω : BrownianPath d)
    (hactive : (brownianSkeletonClock U z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector K ω).2 ≠ ∞)
    (n : ℕ) (hn : n < K) :
    (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal <
      (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal := by
  have hnK : n + 1 ≤ K := Nat.succ_le_of_lt hn
  have hf := brownianSkeletonClock_finite_of_le U z j₀ selector ω hnK hfinite
  have ha := brownianSkeletonClock_active_of_le U z j₀ selector ω hnK hactive
  obtain ⟨j, hj, hout⟩ :=
    brownianSkeletonClock_active_step_exit U hU z j₀ selector n ω ha hf
  have hin := hstart _ _ _ hj
  have hle : (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal ≤
      (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal :=
    ENNReal.toNNReal_mono hf (brownianSkeletonClock_time_le_succ U z j₀ selector n ω)
  apply lt_of_le_of_ne hle
  intro heq
  rw [heq] at hin
  exact hout hin

/-- Clipping preserves strict increase until the cutoff. -/
theorem brownianSkeletonClock_active_clipped_time_lt_succ_of_mem {d : ℕ} {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J)
    (hstart : ∀ n x j, selector n x = some j → x ∈ U j)
    (K : ℕ) (ω : BrownianPath d)
    (hactive : (brownianSkeletonClock U z j₀ selector K ω).1 = false)
    (hfinite : (brownianSkeletonClock U z j₀ selector K ω).2 ≠ ∞)
    (T : ℝ≥0) (n : ℕ) (hn : n < K)
    (hbefore : (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal < T) :
    min (brownianSkeletonClock U z j₀ selector n ω).2.toNNReal T <
      min (brownianSkeletonClock U z j₀ selector (n + 1) ω).2.toNNReal T := by
  rw [min_eq_left hbefore.le]
  exact lt_min (brownianSkeletonClock_active_time_lt_succ_of_mem U hU z j₀ selector hstart
    K ω hactive hfinite n hn) hbefore

/-- Prepending zero preserves strict increase, including the initial excursion. -/
theorem brownianSkeletonClock_prepend_zero_lt_succ_of_mem {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J)
    (hselect : ∀ n x j, selector n x = some j → x ∈ U j)
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
      brownianSkeletonClock_active_time_lt_succ_of_mem U hU z j₀ selector hselect
        K ω hactive hfinite n hn'

/-- Clipping the prepended times preserves strictness before the cutoff. -/
theorem brownianSkeletonClock_prepend_zero_clipped_lt_succ_of_mem {d : ℕ} {J : Type*}
    [Countable J] [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J)
    (hselect : ∀ n x j, selector n x = some j → x ∈ U j)
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
  exact lt_min (brownianSkeletonClock_prepend_zero_lt_succ_of_mem U hU z j₀ selector hselect
    K ω hstart hactive hfinite n hn) hbefore

end BouRabeeGwynne

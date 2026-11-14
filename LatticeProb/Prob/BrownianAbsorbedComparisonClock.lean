import LatticeProb.Prob.BrownianInitialClockStrict
import LatticeProb.Prob.BrownianFirstAbsorption

/-! # Finite absorbed Brownian excursion clocks -/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace BouRabeeGwynne

/-- A finite absorbed skeleton has a globally monotone zero-prepended clock,
which is strict before its terminal value and agrees with the skeleton up to
its terminal stage. -/
theorem brownianSkeletonClock_exists_absorbed_comparison_clock
    {d : ℕ} {J : Type*} [Countable J]
    [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]
    (U : J → Set (Euc d)) (hU : ∀ j, IsOpen (U j)) (z : Euc d) (j₀ : J)
    (selector : ℕ → Euc d → Option J) {ε : ℝ} (hε : 0 < ε)
    (hmargin : ∀ n x j, selector n x = some j → Metric.ball x ε ⊆ U j)
    (K : ℕ) (ω : BrownianPath d) (hstart : z + ω 0 ∈ U j₀)
    (hstop : (brownianSkeletonClock U z j₀ selector K ω).1 = true)
    (hfinite : (brownianSkeletonClock U z j₀ selector K ω).2 ≠ ∞) :
    ∃ T : ℕ → ℝ≥0, T 0 = 0 ∧ Monotone T ∧
      (∀ i ≤ K, T (i + 1) =
        (brownianSkeletonClock U z j₀ selector i ω).2.toNNReal) ∧
      (∀ n < K + 1, T n < T (K + 1) → T n < T (n + 1)) := by
  let T : ℕ → ℝ≥0 := fun n => Nat.casesOn n 0
    (fun i => (brownianSkeletonClock U z j₀ selector (min i K) ω).2.toNNReal)
  have hmono : Monotone T := by
    apply monotone_nat_of_le_succ
    intro n
    cases n with
    | zero => exact zero_le
    | succ n =>
      change (brownianSkeletonClock U z j₀ selector (min n K) ω).2.toNNReal ≤
        (brownianSkeletonClock U z j₀ selector (min (n + 1) K) ω).2.toNNReal
      exact ENNReal.toNNReal_mono
        (brownianSkeletonClock_finite_of_le U z j₀ selector ω (min_le_right _ _) hfinite)
        (brownianSkeletonClock_time_monotone U z j₀ selector ω
          (min_le_min_right K (Nat.le_succ n)))
  have hmatch : ∀ i ≤ K, T (i + 1) =
      (brownianSkeletonClock U z j₀ selector i ω).2.toNNReal := by
    intro i hi
    simp only [T, min_eq_left hi]
  obtain ⟨m, hm, ha, _, heq, htime⟩ :=
    brownianSkeletonClock_exists_last_active U z j₀ selector ω K hstop
  have hfinm : (brownianSkeletonClock U z j₀ selector m ω).2 ≠ ∞ :=
    brownianSkeletonClock_finite_of_le U z j₀ selector ω hm.le hfinite
  have hterminal : T (m + 1) = T (K + 1) := by
    rw [hmatch m hm.le, hmatch K le_rfl, heq, htime]
  refine ⟨T, rfl, hmono, hmatch, ?_⟩
  intro n hn hbefore
  have hnm : n < m + 1 := by
    by_contra h
    have hmle : m + 1 ≤ n := Nat.le_of_not_gt h
    have hle := hmono hmle
    rw [hterminal] at hle
    exact (not_le_of_gt hbefore) hle
  have hstrict := brownianSkeletonClock_prepend_zero_lt_succ U hU z j₀ selector
    hε hmargin m ω hstart ha hfinm n hnm
  cases n with
  | zero =>
    change (0 : ℝ≥0) < (brownianSkeletonClock U z j₀ selector 0 ω).2.toNNReal at hstrict
    change (0 : ℝ≥0) < (brownianSkeletonClock U z j₀ selector (min 0 K) ω).2.toNNReal
    simpa only [min_eq_left (Nat.zero_le K)] using hstrict
  | succ n =>
    have hnK : n ≤ K := by omega
    have hnK' : n + 1 ≤ K := by omega
    simpa only [T, Nat.succ_eq_add_one, Nat.casesOn, min_eq_left hnK,
      min_eq_left hnK'] using hstrict

end BouRabeeGwynne

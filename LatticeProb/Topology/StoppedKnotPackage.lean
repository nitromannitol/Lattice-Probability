import Mathlib

/-!
# Stopping a finite knot sequence

A finite sequence which reaches a cutoff can be clipped at its first crossing.
Strictness and path oscillation before the cutoff then give the interval and
constant-tail conditions for comparison of stopped paths.
-/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.KnotReparam

/-- Clip the knots at the first crossing of a reached cutoff. Strictness is only
needed before the cutoff, so the knots may be constant after crossing. -/
theorem exists_stopped_knot_package {E : Type*} [PseudoMetricSpace E]
    (f : ℝ≥0 → E) (τ : ℕ → ℝ≥0) (T : ℝ≥0) (K : ℕ) (a : ℝ)
    (hzero : τ 0 = 0) (hreach : T ≤ τ K)
    (hstrict : ∀ n < K, τ n < T → τ n < τ (n + 1))
    (hosc : ∀ n < K, ∀ t ∈ Icc (τ n) (τ (n + 1)),
      dist (f t) (f (τ n)) ≤ a) :
    ∃ N ≤ K, (min (τ 0) T = 0) ∧ (min (τ N) T = T) ∧
      (∀ n < N, min (τ n) T < min (τ (n + 1)) T) ∧
      (∀ n < N, ∀ t ∈ Ico (min (τ n) T) (min (τ (n + 1)) T),
        dist (f (min t T)) (f (min (τ n) T)) ≤ a) ∧
      (∀ t, min (τ N) T ≤ t → f (min t T) = f T) := by
  classical
  have hex : ∃ n, T ≤ τ n := ⟨K, hreach⟩
  let N := Nat.find hex
  have hN : T ≤ τ N := Nat.find_spec hex
  have hNK : N ≤ K := Nat.find_min' hex hreach
  have hbefore : ∀ n < N, τ n < T := by
    intro n hn
    exact lt_of_not_ge (Nat.find_min hex hn)
  refine ⟨N, hNK, ?_, min_eq_right hN, ?_, ?_, ?_⟩
  · simp [hzero]
  · intro n hn
    have hnt : τ n < T := hbefore n hn
    rw [min_eq_left hnt.le]
    exact lt_min (hstrict n (lt_of_lt_of_le hn hNK) hnt) hnt
  · intro n hn t ht
    have hnt : τ n < T := hbefore n hn
    have ht0 : τ n ≤ t := by simpa [min_eq_left hnt.le] using ht.1
    have ht1 : t ≤ τ (n + 1) := (le_of_lt ht.2).trans (min_le_left _ _)
    have htT : t ≤ T := (le_of_lt ht.2).trans (min_le_right _ _)
    simpa [min_eq_left htT, min_eq_left hnt.le] using
      hosc n (lt_of_lt_of_le hn hNK) t ⟨ht0, ht1⟩
  · intro t ht
    rw [min_eq_right hN] at ht
    rw [min_eq_right ht]

end LatticeProb.KnotReparam

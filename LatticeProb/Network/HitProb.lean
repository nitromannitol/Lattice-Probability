import LatticeProb.Network.FirstReturn

/-!
# Hitting probability before leaving a set

The hitting probability of a vertex before leaving a set, and its harmonicity.

`hitProb G C o x` is the probability that the walk from `x`, killed on leaving `C`, ever visits
`o`; it is the sum of the first-passage probabilities `firstHit G C o k x`
(`LatticeProb/Network/FirstReturn.lean`).  It is nonnegative, at most one, and — the point of the
module — harmonic at every vertex of `C` other than `o` (`hitProb_laplacian`), which is the
one-step recursion `∑_{y ∼ x} p_k(y) = deg(x) p_{k+1}(x)` summed over `k`.

This is the hitting-probability construction of the voltage function, which survives recurrence
(unlike the Green-function construction of `LatticeProb/Network/Voltage.lean`).

The proof was written by the library's proof fleet from a statement-owned decomposition and
verified by the library gates.
-/

open Finset
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The probability that the walk from `x` ever hits `o` before leaving `C`. -/
noncomputable def hitProb (G : SimpleGraph V) [G.LocallyFinite] (C : Set V) (o : V) (x : V) : ℝ :=
  ∑' k : ℕ, firstHit G C o k x

/-- `hitProb` is nonnegative. -/
theorem hitProb_nonneg (C : Set V) (o : V) (x : V) : 0 ≤ hitProb G C o x :=
  tsum_nonneg fun k => firstHit_nonneg C o k x

/-- `hitProb` is at most one. -/
theorem hitProb_le_one (C : Set V) (o : V) (x : V) : hitProb G C o x ≤ 1 := by
  rw [hitProb]
  refine Real.tsum_le_of_sum_range_le (fun k => firstHit_nonneg C o k x) fun n => ?_
  have hkey : ∀ n, ∀ x, ∑ k ∈ Finset.range (n + 1), firstHit G C o k x ≤ 1 := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [Finset.sum_range_one, firstHit_zero]
      split <;> norm_num
    | succ n ih =>
      intro x
      rw [Finset.sum_range_succ']
      by_cases hx : x = o
      · subst hx
        have hzero : ∀ k, firstHit G C x (k + 1) x = 0 := fun k => firstHit_succ_source C x k
        rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const_zero, zero_add,
          firstHit_zero, if_pos rfl]
      · rw [firstHit_zero, if_neg hx, add_zero]
        by_cases hxC : x ∈ C
        · have hstep : ∀ k, firstHit G C o (k + 1) x
              = (∑ z ∈ G.neighborFinset x, firstHit G C o k z) / G.degree x := fun k => by
            rw [firstHit_succ, if_neg hx, if_pos hxC]
          rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.sum_div]
          refine div_le_one_of_le₀ ?_ (by positivity)
          calc ∑ k ∈ Finset.range (n + 1), ∑ z ∈ G.neighborFinset x, firstHit G C o k z
              = ∑ z ∈ G.neighborFinset x, ∑ k ∈ Finset.range (n + 1), firstHit G C o k z :=
                Finset.sum_comm
            _ ≤ ∑ _z ∈ G.neighborFinset x, (1 : ℝ) :=
                Finset.sum_le_sum fun z _ => ih z
            _ = (G.degree x : ℝ) := by
                rw [Finset.sum_const, nsmul_eq_mul, mul_one]
                rfl
        · have hzero : ∀ k, firstHit G C o (k + 1) x = 0 := fun k => by
            rw [firstHit_succ, if_neg hx, if_neg hxC]
          rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const_zero]
          norm_num
  rcases n with _ | m
  · simp
  · exact hkey m x

/-- The first-passage probabilities are summable in `k`, so `hitProb` is a well-defined series. -/
theorem summable_firstHit (C : Set V) (o : V) (x : V) : Summable fun k => firstHit G C o k x :=
  summable_of_sum_range_le (c := 1) (fun k => firstHit_nonneg C o k x) fun n => by
    have hkey : ∀ n, ∀ x, ∑ k ∈ Finset.range (n + 1), firstHit G C o k x ≤ 1 := by
      intro n
      induction n with
      | zero =>
        intro x
        rw [Finset.sum_range_one, firstHit_zero]
        split <;> norm_num
      | succ n ih =>
        intro x
        rw [Finset.sum_range_succ']
        by_cases hx : x = o
        · subst hx
          have hzero : ∀ k, firstHit G C x (k + 1) x = 0 := fun k => firstHit_succ_source C x k
          rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const_zero, zero_add,
            firstHit_zero, if_pos rfl]
        · rw [firstHit_zero, if_neg hx, add_zero]
          by_cases hxC : x ∈ C
          · have hstep : ∀ k, firstHit G C o (k + 1) x
                = (∑ z ∈ G.neighborFinset x, firstHit G C o k z) / G.degree x := fun k => by
              rw [firstHit_succ, if_neg hx, if_pos hxC]
            rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.sum_div]
            refine div_le_one_of_le₀ ?_ (by positivity)
            calc ∑ k ∈ Finset.range (n + 1), ∑ z ∈ G.neighborFinset x, firstHit G C o k z
                = ∑ z ∈ G.neighborFinset x, ∑ k ∈ Finset.range (n + 1), firstHit G C o k z :=
                  Finset.sum_comm
              _ ≤ ∑ _z ∈ G.neighborFinset x, (1 : ℝ) :=
                  Finset.sum_le_sum fun z _ => ih z
              _ = (G.degree x : ℝ) := by
                  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
                  rfl
          · have hzero : ∀ k, firstHit G C o (k + 1) x = 0 := fun k => by
              rw [firstHit_succ, if_neg hx, if_neg hxC]
            rw [Finset.sum_congr rfl (fun k _ => hzero k), Finset.sum_const_zero]
            norm_num
    rcases n with _ | m
    · simp
    · exact hkey m x

/-- `hitProb` is harmonic at every vertex of `C` other than `o`. -/
theorem hitProb_laplacian (C : Set V) (o : V) {x : V} (hxC : x ∈ C) (hx : x ≠ o) :
    laplacian G (hitProb G C o) x = 0 := by
  have hsum : ∀ y : V, Summable fun k => firstHit G C o k y := fun y => summable_firstHit C o y
  have hstep : ∀ k : ℕ, ∑ y ∈ G.neighborFinset x, firstHit G C o k y
      = (G.degree x : ℝ) * firstHit G C o (k + 1) x := by
    intro k
    rw [firstHit_succ, if_neg hx, if_pos hxC]
    by_cases hd : G.degree x = 0
    · have h2 : (G.neighborFinset x).card = 0 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, hd]
      rw [Finset.card_eq_zero] at h2
      rw [h2, Finset.sum_empty, hd]
      norm_num
    · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd)]
  have hnb : ∑ y ∈ G.neighborFinset x, hitProb G C o y
      = (G.degree x : ℝ) * (∑' k : ℕ, firstHit G C o k x - firstHit G C o 0 x) := by
    have h1 : ∑ y ∈ G.neighborFinset x, hitProb G C o y
        = ∑' k : ℕ, ∑ y ∈ G.neighborFinset x, firstHit G C o k y :=
      (Summable.tsum_finsetSum (fun y _ => hsum y)).symm
    have hsucc : Summable fun k : ℕ => firstHit G C o (k + 1) x :=
      (summable_nat_add_iff 1).mpr (hsum x)
    rw [h1, tsum_congr hstep, hsucc.tsum_mul_left]
    congr 1
    have h := (hsum x).tsum_eq_zero_add
    linarith
  rw [laplacian, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, hnb, hitProb]
  have h0 : firstHit G C o 0 x = if x = o then (1 : ℝ) else 0 := firstHit_zero C o x
  rw [h0, if_neg hx]
  ring


end LatticeProb.Network

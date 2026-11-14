import LatticeProb.Euclidean.GoodExcursionIndexGap

/-! # Zero-prepended anchors for matched excursions -/

set_option autoImplicit false

open Set
open scoped NNReal unitInterval

namespace BouRabeeGwynne

/-- A clipped terminal index with strictly increasing earlier clips is unique. -/
theorem clipped_terminal_index_eq {α : Type*} [LinearOrder α]
    (clockX : ℕ → α) (T : α) (N M : ℕ)
    (hN : min (clockX N) T = T) (hM : min (clockX M) T = T)
    (hNstrict : ∀ n < N, min (clockX n) T < min (clockX (n + 1)) T)
    (hMstrict : ∀ n < M, min (clockX n) T < min (clockX (n + 1)) T) : N = M := by
  apply Nat.le_antisymm
  · by_contra h
    have hlt : M < N := Nat.lt_of_not_ge h
    have hh := hNstrict M hlt
    rw [hM] at hh
    exact (not_lt_of_ge (min_le_right _ _)) hh
  · by_contra h
    have hlt : N < M := Nat.lt_of_not_ge h
    have hh := hMstrict N hlt
    rw [hN] at hh
    exact (not_lt_of_ge (min_le_right _ _)) hh

/-- Matched excursion endpoints control zero-prepended knot anchors. The
initial positions and the index shift are separate hypotheses. -/
theorem goodExcursionPair_shifted_anchor_bounds {d : ℕ} {V X : Type*} [PseudoMetricSpace X]
    (e : Euc d → X) (he : Isometry e)
    (pos : V → Euc d) (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (p : ℕ → (Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d)))
    (f g : ℕ → X) (N M : ℕ) (a : ℝ)
    (hstart : dist (f 0) (g 0) ≤ a)
    (hf : ∀ i ≤ min N M, f (i + 1) = e (ClockedWalkExcursion.endPoint (p i).1.2))
    (hg : ∀ i ≤ min N M, g (i + 1) = e ((p i).2.2 1))
    (hdiam : ∀ i ≤ min N M, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ min N M, p i ∈ goodExcursionPair pos (E i) a) :
    ∀ i ≤ min (N + 1) (M + 1), dist (f i) (g i) ≤ a := by
  intro i hi
  cases i with
  | zero => exact hstart
  | succ i =>
    have hi' : i ≤ min N M := by omega
    rw [hf i hi', hg i hi']
    rw [he.dist_eq]
    exact goodExcursionPair_dist_le pos (E i) (hdiam i hi') (hgood i hi')

/-- Fixed shifted terminal indices supply the universal anchor condition for
strictly clipped knot sequences. -/
theorem goodExcursionPair_universal_clipped_anchor_bounds {d : ℕ} {V X : Type*} [PseudoMetricSpace X]
    (e : Euc d → X) (he : Isometry e)
    (pos : V → Euc d) (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (p : ℕ → (Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d)))
    (f g : ℕ → X) (clockX clockY : ℕ → ℝ≥0) (T S : ℝ≥0) (N M K L : ℕ) (a : ℝ)
    (hstart : dist (f 0) (g 0) ≤ a)
    (hf : ∀ i ≤ min N M, f (i + 1) = e (ClockedWalkExcursion.endPoint (p i).1.2))
    (hg : ∀ i ≤ min N M, g (i + 1) = e ((p i).2.2 1))
    (hdiam : ∀ i ≤ min N M, ∀ j, ∀ x ∈ E i j, ∀ y ∈ E i j, dist x y ≤ a)
    (hgood : ∀ i ≤ min N M, p i ∈ goodExcursionPair pos (E i) a)
    (hgap : N ≤ M + 1 ∧ M ≤ N + 1)
    (hN : min (clockX (N + 1)) T = T) (hM : min (clockY (M + 1)) S = S)
    (hclockX : ∀ i < N + 1, min (clockX i) T < min (clockX (i + 1)) T)
    (hclockY : ∀ i < M + 1, min (clockY i) S < min (clockY (i + 1)) S) :
    ∀ n ≤ K, ∀ q ≤ L,
      min (clockX n) T = T → min (clockY q) S = S →
      (∀ i < n, min (clockX i) T < min (clockX (i + 1)) T) →
      (∀ i < q, min (clockY i) S < min (clockY (i + 1)) S) →
      (∀ i ≤ min n q, dist (f i) (g i) ≤ a) ∧ n ≤ q + 1 ∧ q ≤ n + 1 := by
  intro n _ q _ hn hq hns hqs
  have hn' : n = N + 1 := clipped_terminal_index_eq clockX T n (N + 1) hn hN hns hclockX
  have hq' : q = M + 1 := clipped_terminal_index_eq clockY S q (M + 1) hq hM hqs hclockY
  subst n
  subst q
  refine ⟨goodExcursionPair_shifted_anchor_bounds e he pos m E p f g N M a
    hstart hf hg hdiam hgood, ?_, ?_⟩ <;> omega

end BouRabeeGwynne

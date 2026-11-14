import LatticeProb.Euclidean.ParentBlockCollarComparison

/-! # Parent-block comparison up to terminal skeleton clocks -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

/-- A nondecreasing clock is constant after it reaches its value at a later
finite index. -/
theorem clock_min_eq_of_terminal {α : Type*} [PartialOrder α]
    (τ : ℕ → α) (hτ : Monotone τ) {N K n : ℕ}
    (hN : τ N = τ K) (hn : n ≤ K) : τ (min n N) = τ n := by
  by_cases h : n ≤ N
  · simp [min_eq_left h]
  · have hNn : N ≤ n := Nat.le_of_not_ge h
    have heq : τ n = τ N := le_antisymm ((hτ hn).trans (le_of_eq hN.symm)) (hτ hNn)
    simpa [min_eq_right hNn] using heq.symm

/-- Matching full anchors control two paths stopped at finite terminal clock
values, even when their clocks become constant at different indices. -/
theorem exists_orderIso_dist_le_of_parentBlock_collars_terminal_clocks
    (f g : ℝ≥0 → ℂ) (τ σ : ℕ → ℝ≥0) (K : ℕ)
    (c d : ℕ → ℂ) (s r u v δ : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hτmono : Monotone τ) (hσmono : Monotone σ)
    (hτ : ∀ n < K, τ n < τ K → τ n < τ (n + 1))
    (hσ : ∀ n < K, σ n < σ K → σ n < σ (n + 1))
    (hfstart : ∀ n < K, f (τ n) ∈ closedSquare (c n) s)
    (hgstart : ∀ n < K, g (σ n) ∈ closedSquare (d n) u)
    (hfcollar : ∀ n < K, ∀ t ∈ Icc (τ n) (τ (n + 1)),
      f t ∈ Metric.cthickening r (parentBlock (c n) s))
    (hgcollar : ∀ n < K, ∀ t ∈ Icc (σ n) (σ (n + 1)),
      g t ∈ Metric.cthickening v (parentBlock (d n) u))
    (hanchors : ∀ n ≤ K, dist (f (τ n)) (g (σ n)) ≤ δ) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, ∀ t,
      dist (f (min t (τ K))) (g (min (φ t) (σ K))) ≤
        max (r + 4 * s) (v + 4 * u) + δ + max (r + 4 * s) (v + 4 * u) := by
  apply exists_orderIso_dist_le_of_parentBlock_collars f g τ σ (τ K) (σ K) K K
    c d s r u v δ hs hr hu hv hτ0 hσ0 le_rfl le_rfl hτ hσ
    hfstart hgstart hfcollar hgcollar
  intro N hNK M hMK hN hM _ _ n hn
  have hnK : n ≤ K := by simpa using hn
  have hN' : τ N = τ K := le_antisymm (hτmono hNK) (min_eq_right_iff.mp hN)
  have hM' : σ M = σ K := le_antisymm (hσmono hMK) (min_eq_right_iff.mp hM)
  rw [clock_min_eq_of_terminal τ hτmono hN' hnK,
    clock_min_eq_of_terminal σ hσmono hM' hnK,
    min_eq_left (hτmono hnK), min_eq_left (hσmono hnK)]
  exact hanchors n hnK

end LatticeProb.ParentBlock

import Mathlib

/-! # First clipped indices under crossing brackets -/

set_option autoImplicit false

namespace LatticeProb.KnotReparam

/-- Two first clipped indices differ by at most `J` if crossing either cutoff
forces the other cutoff to be crossed by the corresponding shifted index. -/
theorem clipped_index_gap_of_crossing_brackets {α : Type*} [LinearOrder α]
    (τ σ : ℕ → α) (T S : α) (N M J : ℕ)
    (hN : min (τ N) T = T) (hM : min (σ M) S = S)
    (hτ : ∀ i < N, min (τ i) T < min (τ (i + 1)) T)
    (hσ : ∀ i < M, min (σ i) S < min (σ (i + 1)) S)
    (hτσ : T ≤ τ N → S ≤ σ (N + J))
    (hστ : S ≤ σ M → T ≤ τ (M + J)) :
    N ≤ M + J ∧ M ≤ N + J := by
  have hT : T ≤ τ N := min_eq_right_iff.mp hN
  have hS : S ≤ σ M := min_eq_right_iff.mp hM
  constructor
  · by_contra h
    have hi : M + J < N := Nat.lt_of_not_ge h
    have hlt : min (τ (M + J)) T < T :=
      lt_of_lt_of_le (hτ (M + J) hi) (min_le_right _ _)
    rw [min_eq_right (hστ hS)] at hlt
    exact lt_irrefl _ hlt
  · by_contra h
    have hi : N + J < M := Nat.lt_of_not_ge h
    have hlt : min (σ (N + J)) S < S :=
      lt_of_lt_of_le (hσ (N + J) hi) (min_le_right _ _)
    rw [min_eq_right (hτσ hT)] at hlt
    exact lt_irrefl _ hlt

/-- Global crossing brackets give the terminal-index hypothesis for any first
clipped indices chosen within finite horizons. -/
theorem clipped_index_gap_of_uniform_crossing_brackets {α : Type*} [LinearOrder α]
    (τ σ : ℕ → α) (T S : α) (K L J : ℕ)
    (hτσ : ∀ i ≤ K, T ≤ τ i → S ≤ σ (i + J))
    (hστ : ∀ i ≤ L, S ≤ σ i → T ≤ τ (i + J)) :
    ∀ N ≤ K, ∀ M ≤ L,
      min (τ N) T = T → min (σ M) S = S →
      (∀ i < N, min (τ i) T < min (τ (i + 1)) T) →
      (∀ i < M, min (σ i) S < min (σ (i + 1)) S) →
      N ≤ M + J ∧ M ≤ N + J := by
  intro N hNK M hML hN hM hτ hσ
  exact clipped_index_gap_of_crossing_brackets τ σ T S N M J hN hM hτ hσ
    (hτσ N hNK) (hστ M hML)

end LatticeProb.KnotReparam

import LatticeProb.Euclidean.ParentBlockCollar

/-! # Anchor tails for parent-block paths -/

set_option autoImplicit false

open Set
open scoped NNReal

namespace LatticeProb.ParentBlock

/-- A bound on the number of knot intervals controls the distance between
anchors of a path whose segments remain in parent-block collars. -/
theorem dist_knots_le_of_parentBlock_collars
    (f : ℝ≥0 → ℂ) (τ : ℕ → ℝ≥0) (c : ℕ → ℂ) (N : ℕ) (s r : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hτ : ∀ k < N, τ k ≤ τ (k + 1))
    (hstart : ∀ k < N, f (τ k) ∈ closedSquare (c k) s)
    (hcollar : ∀ k < N, ∀ t ∈ Icc (τ k) (τ (k + 1)),
      f t ∈ Metric.cthickening r (parentBlock (c k) s))
    (j i J : ℕ) (hji : j ≤ i) (hi : i ≤ N) (hgap : i - j ≤ J) :
    dist (f (τ j)) (f (τ i)) ≤ (J : ℝ) * (r + 4 * s) := by
  have ha : 0 ≤ r + 4 * s := by positivity
  have hsum := dist_le_Ico_sum_of_dist_le (f := fun k => f (τ k))
    (d := fun _ => r + 4 * s) hji (by
      intro k _ hk
      have hkN : k < N := lt_of_lt_of_le hk hi
      have h := dist_le_of_mem_cthickening_subset_parentBlock hs hr (hstart k hkN)
        Subset.rfl (hcollar k hkN (τ (k + 1)) ⟨hτ k hkN, le_rfl⟩)
      simpa only [dist_comm] using h)
  calc
    dist (f (τ j)) (f (τ i)) ≤ (↑(i - j) : ℝ) * (r + 4 * s) := by
      simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] using hsum
    _ ≤ (J : ℝ) * (r + 4 * s) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hgap) ha

/-- If the terminal knot indices differ by at most `J`, the unmatched anchors
of either path are controlled by the same collar-dependent bound. -/
theorem anchor_tails_le_of_parentBlock_collars
    (f g : ℝ≥0 → ℂ) (τ σ : ℕ → ℝ≥0) (c d : ℕ → ℂ)
    (N M J : ℕ) (s r u v : ℝ)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hτ : ∀ k < N, τ k ≤ τ (k + 1))
    (hσ : ∀ k < M, σ k ≤ σ (k + 1))
    (hfstart : ∀ k < N, f (τ k) ∈ closedSquare (c k) s)
    (hgstart : ∀ k < M, g (σ k) ∈ closedSquare (d k) u)
    (hfcollar : ∀ k < N, ∀ t ∈ Icc (τ k) (τ (k + 1)),
      f t ∈ Metric.cthickening r (parentBlock (c k) s))
    (hgcollar : ∀ k < M, ∀ t ∈ Icc (σ k) (σ (k + 1)),
      g t ∈ Metric.cthickening v (parentBlock (d k) u))
    (hNM : N ≤ M + J) (hMN : M ≤ N + J) :
    (∀ i, M ≤ i → i ≤ N → dist (f (τ i)) (f (τ M)) ≤
      (J : ℝ) * max (r + 4 * s) (v + 4 * u)) ∧
    (∀ i, N ≤ i → i ≤ M → dist (g (σ N)) (g (σ i)) ≤
      (J : ℝ) * max (r + 4 * s) (v + 4 * u)) := by
  constructor
  · intro i hMi hiN
    have hgap : i - M ≤ J := by omega
    have h := dist_knots_le_of_parentBlock_collars f τ c N s r hs hr hτ hfstart hfcollar
      M i J hMi hiN hgap
    rw [dist_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg J))
  · intro i hNi hiM
    have hgap : i - N ≤ J := by omega
    have h := dist_knots_le_of_parentBlock_collars g σ d M u v hu hv hσ hgstart hgcollar
      N i J hNi hiM hgap
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg J))

end LatticeProb.ParentBlock

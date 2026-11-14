import LatticeProb.Topology.KnotReparametrization

/-!
# Comparison of paths with separately stopped knot sequences

Finite skeletons may stop at different indices. Extending their time sequences
and holding their last anchors fixed allows the usual knot comparison to be
applied when the padded anchors are close.
-/

open Set
open scoped NNReal

namespace LatticeProb.KnotReparam

/-- Compare two paths whose finite knot sequences can stop at different indices.
The anchor comparison includes the padded portions of both skeletons. -/
theorem exists_orderIso_dist_le_of_asymmetric_finite_knots
    {E : Type*} [PseudoMetricSpace E] {f g : ℝ≥0 → E}
    {τ σ : ℕ → ℝ≥0} {N M K : ℕ} (hNK : N ≤ K) (hMK : M ≤ K)
    (hτ : ∀ n < N, τ n < τ (n + 1)) (hσ : ∀ n < M, σ n < σ (n + 1))
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) {p q : ℕ → E} {a δ : ℝ}
    (hpq : ∀ n ≤ K, dist (p (min n N)) (q (min n M)) ≤ δ)
    (hf : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), dist (f t) (p n) ≤ a)
    (hg : ∀ n < M, ∀ t ∈ Ico (σ n) (σ (n + 1)), dist (g t) (q n) ≤ a)
    (hfN : ∀ t, τ N ≤ t → dist (f t) (p N) ≤ a)
    (hgM : ∀ t, σ M ≤ t → dist (g t) (q M) ≤ a) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, (∀ n ≤ min N M, φ (τ n) = σ n) ∧
      ∀ t, dist (f t) (g (φ t)) ≤ a + δ + a := by
  have hτ0' : extendKnots τ N 0 = 0 := by rw [extendKnots_of_le (Nat.zero_le N), hτ0]
  have hσ0' : extendKnots σ M 0 = 0 := by rw [extendKnots_of_le (Nat.zero_le M), hσ0]
  have hf' : ∀ n, ∀ t ∈ Ico (extendKnots τ N n) (extendKnots τ N (n + 1)),
      dist (f t) (p (min n N)) ≤ a := by
    intro n t ht
    rcases lt_or_ge n N with hn | hn
    · rw [extendKnots_of_le hn.le, extendKnots_of_le hn] at ht
      rw [min_eq_left hn.le]
      exact hf n hn t ht
    · rw [min_eq_right hn]
      exact hfN t ((le_extendKnots hn).trans ht.1)
  have hg' : ∀ n, ∀ t ∈ Ico (extendKnots σ M n) (extendKnots σ M (n + 1)),
      dist (g t) (q (min n M)) ≤ a := by
    intro n t ht
    rcases lt_or_ge n M with hn | hn
    · rw [extendKnots_of_le hn.le, extendKnots_of_le hn] at ht
      rw [min_eq_left hn.le]
      exact hg n hn t ht
    · rw [min_eq_right hn]
      exact hgM t ((le_extendKnots hn).trans ht.1)
  have hpq' : ∀ n, dist (p (min n N)) (q (min n M)) ≤ δ := by
    intro n
    by_cases hn : n ≤ K
    · exact hpq n hn
    · have hKn : K ≤ n := le_of_not_ge hn
      have h := hpq K le_rfl
      rw [min_eq_right hNK, min_eq_right hMK] at h
      rw [min_eq_right (hNK.trans hKn), min_eq_right (hMK.trans hKn)]
      exact h
  obtain ⟨φ, hφ, hdist⟩ := exists_orderIso_dist_le_of_knots
    (strictMono_extendKnots hτ) (strictMono_extendKnots hσ) hτ0' hσ0'
    (exists_lt_extendKnots τ N) (exists_lt_extendKnots σ M) hpq' hf' hg'
  refine ⟨φ, ?_, hdist⟩
  intro n hn
  have h := hφ n
  rwa [extendKnots_of_le (hn.trans (min_le_left N M)),
    extendKnots_of_le (hn.trans (min_le_right N M))] at h

end LatticeProb.KnotReparam

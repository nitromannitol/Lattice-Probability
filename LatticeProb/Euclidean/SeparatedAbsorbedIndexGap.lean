import LatticeProb.Euclidean.ParentBlockSeparation

/-! # Terminal indices of matched absorbed chains -/

set_option autoImplicit false

namespace LatticeProb

/-- If a chain has well-separated complete steps while a nearby chain has
already become constant, the first chain has at most one final step left. -/
theorem terminal_index_le_add_one_of_absorbed_close {X : Type*} [PseudoMetricSpace X]
    (a b : ℕ → X) (N M : ℕ) (δ r : ℝ)
    (hr : 2 * δ < r)
    (hclose : ∀ i ≤ M + 1, dist (a i) (b i) ≤ δ)
    (habsorb : ∀ i, M ≤ i → b i = b M)
    (hsep : ∀ i, i + 1 < N → r ≤ dist (a i) (a (i + 1))) :
    N ≤ M + 1 := by
  by_contra hn
  have hN : M + 1 < N := by omega
  have h1 := hclose M (by omega)
  have h2 := hclose (M + 1) le_rfl
  have heq : b (M + 1) = b M := habsorb (M + 1) (by omega)
  rw [heq] at h2
  have hdist : dist (a M) (a (M + 1)) ≤ 2 * δ := by
    calc
      dist (a M) (a (M + 1)) ≤
          dist (a M) (b M) + dist (b M) (a (M + 1)) := dist_triangle _ _ _
      _ ≤ dist (a M) (b M) + dist (b M) (b (M + 1)) +
          dist (b (M + 1)) (a (M + 1)) := by
            linarith [dist_triangle (b M) (b (M + 1)) (a (M + 1))]
      _ ≤ 2 * δ := by rw [heq, dist_self, dist_comm (b M)]; linarith
  linarith [hsep M hN]

/-- Two matched absorbed chains with separated complete steps have terminal
indices differing by at most one; their last steps need not be separated. -/
theorem terminal_indices_close_of_absorbed_close {X : Type*} [PseudoMetricSpace X]
    (a b : ℕ → X) (N M : ℕ) (δ r : ℝ)
    (hr : 2 * δ < r)
    (hclose : ∀ i ≤ max N M, dist (a i) (b i) ≤ δ)
    (ha : ∀ i, N ≤ i → a i = a N)
    (hb : ∀ i, M ≤ i → b i = b M)
    (hasep : ∀ i, i + 1 < N → r ≤ dist (a i) (a (i + 1)))
    (hbsep : ∀ i, i + 1 < M → r ≤ dist (b i) (b (i + 1))) :
    N ≤ M + 1 ∧ M ≤ N + 1 := by
  constructor
  · by_cases h : N ≤ M + 1
    · exact h
    · apply terminal_index_le_add_one_of_absorbed_close a b N M δ r hr _ hb hasep
      intro i hi
      apply hclose i
      have : M + 1 ≤ N := by omega
      exact hi.trans (this.trans (le_max_left _ _))
  · by_cases h : M ≤ N + 1
    · exact h
    · apply terminal_index_le_add_one_of_absorbed_close b a M N δ r hr _ ha hbsep
      intro i hi
      have : N + 1 ≤ M := by omega
      have hi' : i ≤ max N M := hi.trans (this.trans (le_max_right _ _))
      simpa only [dist_comm] using hclose i hi'

/-- A chain of parent-block exits has at most one final step after a
nearby absorbed chain stops. The last step may be cut short by another exit. -/
theorem terminal_index_le_add_one_of_parentBlock_exits
    (a b : ℕ → ℂ) (c : ℕ → ℂ) (N M : ℕ) (δ s : ℝ)
    (hs : 0 ≤ s) (hδ : 2 * δ < s)
    (hclose : ∀ i ≤ M + 1, dist (a i) (b i) ≤ δ)
    (habsorb : ∀ i, M ≤ i → b i = b M)
    (hstart : ∀ i, i + 1 < N → a i ∈ ParentBlock.closedSquare (c i) s)
    (hexit : ∀ i, i + 1 < N →
      a (i + 1) ∉ interior (ParentBlock.parentBlock (c i) s)) :
    N ≤ M + 1 := by
  apply terminal_index_le_add_one_of_absorbed_close a b N M δ s hδ hclose habsorb
  intro i hi
  have h := ParentBlock.side_le_norm_sub_of_not_mem_interior_parentBlock hs
    (hstart i hi) (hexit i hi)
  rw [dist_comm, dist_eq_norm]
  exact h

end LatticeProb

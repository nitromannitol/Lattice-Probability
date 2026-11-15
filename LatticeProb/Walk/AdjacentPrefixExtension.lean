import Mathlib

/-! # Extending a finite path along its last edge -/

set_option autoImplicit false

namespace LatticeProb

/-- Extend a finite path by traversing its last edge alternately in each direction. -/
def alternateLastEdge {V : Type*} (x : ℕ → V) (k : ℕ) (n : ℕ) : V :=
  if n ≤ k then x n else if (n - k) % 2 = 0 then x k else x (k + 1)

/-- The extension agrees with the original path through its last edge. -/
theorem alternateLastEdge_eq {V : Type*} (x : ℕ → V) (k n : ℕ) (hn : n ≤ k + 1) :
    alternateLastEdge x k n = x n := by
  by_cases h : n ≤ k
  · simp [alternateLastEdge, h]
  · have hn' : n = k + 1 := by omega
    subst n
    simp [alternateLastEdge]

/-- Every edge of the extension is an original prefix edge or the reverse of its last edge. -/
theorem alternateLastEdge_edges {V : Type*} (x : ℕ → V) (k n : ℕ) :
    (∃ j ≤ k, alternateLastEdge x k n = x j ∧
      alternateLastEdge x k (n + 1) = x (j + 1)) ∨
    (alternateLastEdge x k n = x (k + 1) ∧
      alternateLastEdge x k (n + 1) = x k) := by
  by_cases h : n ≤ k
  · left
    exact ⟨n, h, alternateLastEdge_eq x k n (by omega),
      alternateLastEdge_eq x k (n + 1) (by omega)⟩
  · have hn : k < n := by omega
    have hn' : ¬ n + 1 ≤ k := by omega
    have hmod : (n - k) % 2 = 0 ∨ (n - k) % 2 = 1 := by omega
    rcases hmod with heven | hodd
    · left
      refine ⟨k, le_rfl, ?_, ?_⟩
      · simp [alternateLastEdge, h, heven]
      · have hnmod : (n + 1 - k) % 2 = 1 := by omega
        simp [alternateLastEdge, hn', hnmod]
    · right
      have hnmod : (n + 1 - k) % 2 = 0 := by omega
      constructor
      · simp [alternateLastEdge, h, hodd]
      · simp [alternateLastEdge, hn', hnmod]

/-- A finite path in a symmetric relation extends to an infinite path in that relation. -/
theorem alternateLastEdge_adjacent {V : Type*} (R : V → V → Prop)
    (hsymm : ∀ ⦃a b⦄, R a b → R b a) (x : ℕ → V) (k : ℕ)
    (hpath : ∀ j ≤ k, R (x j) (x (j + 1))) :
    ∀ n, R (alternateLastEdge x k n) (alternateLastEdge x k (n + 1)) := by
  intro n
  rcases alternateLastEdge_edges x k n with ⟨j, hj, h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
    exact hpath j hj
  · rw [h₁, h₂]
    exact hsymm (hpath k le_rfl)

end LatticeProb

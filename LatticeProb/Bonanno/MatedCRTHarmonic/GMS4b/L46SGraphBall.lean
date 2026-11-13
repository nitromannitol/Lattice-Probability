/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SGraphBall at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Finite graph ball counting

On a finite graph of maximum degree `D`, a ball obtained by at most `k`
closed-neighborhood steps has at most `(D + 1)^k` vertices. This is the
deterministic counting step in the proposed replacement for [18] Lemma 4.6.
-/

set_option autoImplicit false
noncomputable section

namespace MatedCRTHarmonic.GMS4b

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex and all its neighbors in a finite graph. -/
private def l46sClosedNeighbor (v : V) : Finset V := by
  classical
  exact insert v (Finset.univ.filter (fun w => G.Adj v w))

/-- Vertices reached from `x` in at most `k` adjacency steps. -/
def l46sGraphBall (x : V) : ℕ → Finset V
  | 0 => {x}
  | k + 1 => (l46sGraphBall x k).biUnion
      (l46sClosedNeighbor G)

/-- An elementary bound for one closed-neighborhood step. -/
theorem l46sGraphBall_step_card_le (x : V) (k D : ℕ)
    (hD : ∀ v : V, (Finset.univ.filter (fun w => G.Adj v w)).card ≤ D) :
    (l46sGraphBall G x (k + 1)).card ≤
      (l46sGraphBall G x k).card * (D + 1) := by
  classical
  change ((l46sGraphBall G x k).biUnion (l46sClosedNeighbor G)).card ≤ _
  apply Finset.card_biUnion_le_card_mul
  intro v _
  calc
    (l46sClosedNeighbor G v).card ≤
        (Finset.univ.filter (fun w => G.Adj v w)).card + 1 := by
      unfold l46sClosedNeighbor
      exact Finset.card_insert_le _ _
    _ ≤ D + 1 := Nat.add_le_add_right (hD v) 1

/-- A finite graph of maximum degree `D` has at most `(D+1)^k` vertices
within `k` steps of any root. -/
theorem l46sGraphBall_card_le (x : V) (k D : ℕ)
    (hD : ∀ v : V, (Finset.univ.filter (fun w => G.Adj v w)).card ≤ D) :
    (l46sGraphBall G x k).card ≤ (D + 1) ^ k := by
  induction k with
  | zero => simp [l46sGraphBall]
  | succ k ih =>
    calc
      (l46sGraphBall G x (k + 1)).card ≤
          (l46sGraphBall G x k).card * (D + 1) :=
        l46sGraphBall_step_card_le G x k D hD
      _ ≤ (D + 1) ^ k * (D + 1) := Nat.mul_le_mul_right _ ih
      _ = (D + 1) ^ (k + 1) := by ring

/-- A graph neighbor of a vertex already in the `k`-ball belongs to the
`k+1`-ball. -/
theorem l46sGraphBall_step_of_adj {x v w : V} {k : ℕ}
    (hv : v ∈ l46sGraphBall G x k) (hvw : G.Adj v w) :
    w ∈ l46sGraphBall G x (k + 1) := by
  classical
  change w ∈ (l46sGraphBall G x k).biUnion (l46sClosedNeighbor G)
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_insert_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw⟩)⟩

/-- Adjoining one graph edge to the start of a walk adds at most one
closed-neighborhood step to its endpoint ball. -/
theorem l46sGraphBall_mem_of_adj_start {x v y : V} (hxv : G.Adj x v)
    {k : ℕ} (hy : y ∈ l46sGraphBall G v k) :
    y ∈ l46sGraphBall G x (k + 1) := by
  induction k generalizing y with
  | zero =>
    have hyx : y = v := by simpa [l46sGraphBall] using hy
    subst hyx
    exact l46sGraphBall_step_of_adj G (by simp [l46sGraphBall]) hxv
  | succ k ih =>
    change y ∈ (l46sGraphBall G v k).biUnion (l46sClosedNeighbor G) at hy
    obtain ⟨u, hu, huy⟩ := Finset.mem_biUnion.mp hy
    have hux := ih hu
    rcases Finset.mem_insert.mp huy with rfl | hadj
    · exact (by
        classical
        change y ∈ (l46sGraphBall G x (k + 1)).biUnion (l46sClosedNeighbor G)
        exact Finset.mem_biUnion.mpr ⟨y, hux, Finset.mem_insert_self _ _⟩)
    · exact l46sGraphBall_step_of_adj G hux (Finset.mem_filter.mp hadj).2

/-- The endpoint of a walk of length `k` belongs to the `k`-step graph ball. -/
theorem l46sGraphBall_mem_of_walk {x y : V} (p : G.Walk x y) :
    y ∈ l46sGraphBall G x p.length := by
  induction p with
  | nil => simp [l46sGraphBall]
  | cons h p ih =>
    simpa only [SimpleGraph.Walk.length_cons] using
      l46sGraphBall_mem_of_adj_start G h ih

/-- Each closed-neighborhood ball is contained in the next. -/
theorem l46sGraphBall_mono_step (x : V) (k : ℕ) :
    l46sGraphBall G x k ⊆ l46sGraphBall G x (k + 1) := by
  classical
  intro v hv
  change v ∈ (l46sGraphBall G x k).biUnion (l46sClosedNeighbor G)
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_insert_self _ _⟩

/-- A walk endpoint belongs to every ball whose radius exceeds its length. -/
theorem l46sGraphBall_mem_of_walk_le {x y : V} (p : G.Walk x y)
    {k : ℕ} (hk : p.length ≤ k) :
    y ∈ l46sGraphBall G x k := by
  have hmono : ∀ n m : ℕ, n ≤ m →
      l46sGraphBall G x n ⊆ l46sGraphBall G x m := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact Finset.Subset.rfl
    | succ m _ ih => exact ih.trans (l46sGraphBall_mono_step G x m)
  exact hmono _ _ hk (l46sGraphBall_mem_of_walk G p)

/-- Three root vertices have at most three times one ball's maximum size
within `k` graph steps. -/
theorem l46sGraphBall_three_card_le (x₁ x₂ x₃ : V) (k D : ℕ)
    (hD : ∀ v : V, (Finset.univ.filter (fun w => G.Adj v w)).card ≤ D) :
    ((l46sGraphBall G x₁ k ∪ l46sGraphBall G x₂ k) ∪
      l46sGraphBall G x₃ k).card ≤ 3 * (D + 1) ^ k := by
  have h₁ := l46sGraphBall_card_le G x₁ k D hD
  have h₂ := l46sGraphBall_card_le G x₂ k D hD
  have h₃ := l46sGraphBall_card_le G x₃ k D hD
  have hu₁ := Finset.card_union_le (l46sGraphBall G x₁ k)
    (l46sGraphBall G x₂ k)
  have hu₂ := Finset.card_union_le
    (l46sGraphBall G x₁ k ∪ l46sGraphBall G x₂ k)
    (l46sGraphBall G x₃ k)
  nlinarith

end MatedCRTHarmonic.GMS4b

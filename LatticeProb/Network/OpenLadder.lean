import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# The finite open ladder

The vertices are exactly the integer sites in `[1,4] × {1} ∪ {2,3} × [1,n]`.
The graph includes every lattice nearest-neighbor edge between these vertices.
The two terminal sites are leaves; all rung neighbor sets are computed explicitly.
-/

namespace LatticeProb.Network.OpenLadder

noncomputable section

/-- The literal finite set of open sites, with no surrounding closed sites. -/
def vertices (n : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Icc 1 4 ×ˢ {1}) ∪ ({2, 3} ×ˢ Finset.Icc 1 n)

/-- A vertex is an actual open integer site. -/
abbrev Vertex (n : ℤ) := {v // v ∈ vertices n}

/-- The open carrier is finite. -/
instance (n : ℤ) : Fintype (Vertex n) := inferInstance

/-- Membership in the literal open carrier, in coordinates. -/
theorem mem_vertices (n x y : ℤ) :
    (x, y) ∈ vertices n ↔
      (1 ≤ x ∧ x ≤ 4 ∧ y = 1) ∨ ((x = 2 ∨ x = 3) ∧ 1 ≤ y ∧ y ≤ n) := by
  simp only [vertices, Finset.mem_union, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_singleton, Finset.mem_insert]
  tauto

/-- The nearest-neighbor graph on the actual finite open carrier. -/
def graph (n : ℤ) : SimpleGraph (Vertex n) where
  Adj v w :=
    (v.val.1 = w.val.1 ∧ (v.val.2 + 1 = w.val.2 ∨ w.val.2 + 1 = v.val.2)) ∨
    (v.val.2 = w.val.2 ∧ (v.val.1 + 1 = w.val.1 ∨ w.val.1 + 1 = v.val.1))
  symm := ⟨by intro v w; omega⟩
  loopless := ⟨by intro v; omega⟩

/-- The coordinate description of adjacency has a decision procedure. -/
instance (n : ℤ) : DecidableRel (graph n).Adj := fun _ _ => by unfold graph; infer_instance

/-- The left terminal. -/
def source (n : ℤ) : Vertex n :=
  ⟨(1, 1), (mem_vertices n 1 1).mpr (Or.inl ⟨by omega, by omega, rfl⟩)⟩

/-- The right terminal. -/
def target (n : ℤ) : Vertex n :=
  ⟨(4, 1), (mem_vertices n 4 1).mpr (Or.inl ⟨by omega, by omega, rfl⟩)⟩

/-- The left vertex of a rung in the actual carrier. -/
def left (n j : ℤ) (hj : 1 ≤ j ∧ j ≤ n) : Vertex n :=
  ⟨(2, j), (mem_vertices n 2 j).mpr (Or.inr ⟨Or.inl rfl, hj⟩)⟩

/-- The right vertex of a rung in the actual carrier. -/
def right (n j : ℤ) (hj : 1 ≤ j ∧ j ≤ n) : Vertex n :=
  ⟨(3, j), (mem_vertices n 3 j).mpr (Or.inr ⟨Or.inr rfl, hj⟩)⟩

/-- Every nonterminal vertex belongs to one of the actual rungs. -/
theorem eq_left_or_right {n : ℤ} (hn : 1 ≤ n) (v : Vertex n)
    (hs : v ≠ source n) (ht : v ≠ target n) :
    ∃ (j : ℤ) (hj : 1 ≤ j ∧ j ≤ n), v = left n j hj ∨ v = right n j hj := by
  rcases v with ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  have hxs : ¬ (x = 1 ∧ y = 1) := by
    rintro ⟨rfl, rfl⟩; exact hs rfl
  have hxt : ¬ (x = 4 ∧ y = 1) := by
    rintro ⟨rfl, rfl⟩; exact ht rfl
  have hxy : (x = 2 ∨ x = 3) ∧ 1 ≤ y ∧ y ≤ n := by
    rcases hm with h | h
    · have hy := h.2.2
      have hx : x = 2 ∨ x = 3 := by omega
      exact ⟨hx, by omega, by omega⟩
    · exact h
  refine ⟨y, hxy.2, ?_⟩
  rcases hxy.1 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The exact neighbors at the source site. -/
theorem neighbors_source {n : ℤ} (hn : 1 ≤ n) :
    (graph n).neighborFinset (source n) =
      {left n 1 ⟨by omega, hn⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, source, left,
    Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the target site. -/
theorem neighbors_target {n : ℤ} (hn : 1 ≤ n) :
    (graph n).neighborFinset (target n) =
      {right n 1 ⟨by omega, hn⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, target, right,
    Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the left one site. -/
theorem neighbors_left_one :
    (graph 1).neighborFinset (left 1 1 ⟨by omega, by omega⟩) =
      {source 1, right 1 1 ⟨by omega, by omega⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices 1 x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, source, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the right one site. -/
theorem neighbors_right_one :
    (graph 1).neighborFinset (right 1 1 ⟨by omega, by omega⟩) =
      {left 1 1 ⟨by omega, by omega⟩, target 1} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices 1 x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, target, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the left bottom site. -/
theorem neighbors_left_bottom {n : ℤ} (hn : 2 ≤ n) :
    (graph n).neighborFinset (left n 1 ⟨by omega, by omega⟩) =
      {source n, right n 1 ⟨by omega, by omega⟩, left n 2 ⟨by omega, hn⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, source, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the right bottom site. -/
theorem neighbors_right_bottom {n : ℤ} (hn : 2 ≤ n) :
    (graph n).neighborFinset (right n 1 ⟨by omega, by omega⟩) =
      {target n, left n 1 ⟨by omega, by omega⟩, right n 2 ⟨by omega, hn⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, target, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the left middle site. -/
theorem neighbors_left_middle {n j : ℤ} (hj : 1 < j) (hjn : j < n) :
    (graph n).neighborFinset (left n j ⟨by omega, by omega⟩) =
      {right n j ⟨by omega, by omega⟩,
        left n (j - 1) ⟨by omega, by omega⟩,
        left n (j + 1) ⟨by omega, by omega⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the right middle site. -/
theorem neighbors_right_middle {n j : ℤ} (hj : 1 < j) (hjn : j < n) :
    (graph n).neighborFinset (right n j ⟨by omega, by omega⟩) =
      {left n j ⟨by omega, by omega⟩,
        right n (j - 1) ⟨by omega, by omega⟩,
        right n (j + 1) ⟨by omega, by omega⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the left top site. -/
theorem neighbors_left_top {n : ℤ} (hn : 2 ≤ n) :
    (graph n).neighborFinset (left n n ⟨by omega, by omega⟩) =
      {right n n ⟨by omega, by omega⟩, left n (n - 1) ⟨by omega, by omega⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

/-- The exact neighbors at the right top site. -/
theorem neighbors_right_top {n : ℤ} (hn : 2 ≤ n) :
    (graph n).neighborFinset (right n n ⟨by omega, by omega⟩) =
      {left n n ⟨by omega, by omega⟩, right n (n - 1) ⟨by omega, by omega⟩} := by
  ext ⟨⟨x, y⟩, hv⟩
  have hm := (mem_vertices n x y).mp hv
  simp only [SimpleGraph.mem_neighborFinset, graph, left, right,
    Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, Prod.mk.injEq]
  omega

end

end LatticeProb.Network.OpenLadder

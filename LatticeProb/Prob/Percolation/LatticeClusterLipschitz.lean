import LatticeProb.Prob.Percolation.LatticeBondGraph
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Lipschitz functions on actual open components

The source graph-distance inequality uses one finite real constant on the actual component.
Shortest walks give its equivalent uniform bound on open edges, with the same constant.
Every pair in the component has finite distance, by the component's intrinsic connectedness.
-/

namespace LatticeProb.Network

/-- A uniform edge bound propagates along a finite unit-edge walk by the triangle inequality. -/
theorem abs_sub_le_mul_walk_length {V : Type*} {G : SimpleGraph V} (u : V → ℝ)
    {K : ℝ} (hedge : ∀ x y, G.Adj x y → |u x - u y| ≤ K)
    {x y : V} (p : G.Walk x y) : |u x - u y| ≤ K * (p.length : ℝ) := by
  induction p with
  | nil => simp only [sub_self, abs_zero, SimpleGraph.Walk.length_nil, Nat.cast_zero, mul_zero,
      le_refl]
  | @cons x y z h p ih =>
    calc
      |u x - u z| ≤ |u x - u y| + |u y - u z| := abs_sub_le _ _ _
      _ ≤ K + K * (p.length : ℝ) := add_le_add (hedge x y h) ih
      _ = K * ((SimpleGraph.Walk.cons h p).length : ℝ) := by
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        ring

/-- On reachable vertices an edge bound controls the genuine shortest-walk distance. -/
theorem abs_sub_le_mul_graph_dist_of_edge_bound {V : Type*} {G : SimpleGraph V}
    (u : V → ℝ) {K : ℝ} (hedge : ∀ x y, G.Adj x y → |u x - u y| ≤ K)
    {x y : V} (hxy : G.Reachable x y) : |u x - u y| ≤ K * (G.dist x y : ℝ) := by
  obtain ⟨p, hp⟩ := hxy.exists_walk_length_eq_dist
  rw [← hp]
  exact abs_sub_le_mul_walk_length u hedge p

end LatticeProb.Network

namespace LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Source Lipschitzness: one nonnegative finite real constant bounds all graph differences. -/
def ComponentLipschitz (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : C, |u x - u y| ≤ K * ((componentGraph C).dist x y : ℝ)

/-- Actual component vertices always have finite extended graph distance. -/
theorem component_edist_ne_top (C : OpenComponent ω) (x y : C) :
    (componentGraph C).edist x y ≠ ⊤ :=
  SimpleGraph.edist_ne_top_iff_reachable.mpr (C.connected_toSimpleGraph x y)

/-- The natural distance is exactly the finite extended distance, never an unreachable value. -/
theorem component_coe_dist_eq_edist (C : OpenComponent ω) (x y : C) :
    ((componentGraph C).dist x y : ℕ∞) = (componentGraph C).edist x y :=
  (C.connected_toSimpleGraph x y).coe_dist_eq_edist

/-- Every component distance is attained by an actual shortest open walk. -/
theorem component_exists_shortest_walk (C : OpenComponent ω) (x y : C) :
    ∃ p : (componentGraph C).Walk x y, p.length = (componentGraph C).dist x y :=
  C.connected_toSimpleGraph.exists_walk_length_eq_dist x y

/-- Distinct component vertices have strictly positive distance. -/
theorem component_dist_eq_zero_iff (C : OpenComponent ω) (x y : C) :
    (componentGraph C).dist x y = 0 ↔ x = y :=
  C.connected_toSimpleGraph.dist_eq_zero_iff

/-- For each real constant the global inequality is equivalent to the bound on actual edges. -/
theorem component_dist_bound_iff_edge_bound (C : OpenComponent ω) (u : C → ℝ) (K : ℝ) :
    (∀ x y : C, |u x - u y| ≤ K * ((componentGraph C).dist x y : ℝ)) ↔
      (∀ x y : C, (componentGraph C).Adj x y → |u x - u y| ≤ K) := by
  constructor
  · intro h x y hxy
    simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr hxy, Nat.cast_one, mul_one] using h x y
  · intro h x y
    exact Network.abs_sub_le_mul_graph_dist_of_edge_bound u h (C.connected_toSimpleGraph x y)

/-- Source Lipschitzness is precisely a single nonnegative uniform bound on open edges. -/
theorem componentLipschitz_iff_edge_bound (C : OpenComponent ω) (u : C → ℝ) :
    ComponentLipschitz C u ↔
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : C, (componentGraph C).Adj x y → |u x - u y| ≤ K := by
  simp only [ComponentLipschitz, component_dist_bound_iff_edge_bound]

/-- An unrestricted source real constant can always be enlarged to its maximum with zero. -/
theorem componentLipschitz_iff_exists_real_bound (C : OpenComponent ω) (u : C → ℝ) :
    ComponentLipschitz C u ↔
      ∃ K : ℝ, ∀ x y : C, |u x - u y| ≤ K * ((componentGraph C).dist x y : ℝ) := by
  constructor
  · rintro ⟨K, _, h⟩
    exact ⟨K, h⟩
  · rintro ⟨K, h⟩
    refine ⟨max K 0, le_max_right _ _, fun x y => (h x y).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)

/-- Constant functions are Lipschitz with constant zero on every actual component. -/
theorem componentLipschitz_const (C : OpenComponent ω) (a : ℝ) :
    ComponentLipschitz C (fun _ => a) := by
  refine ⟨0, le_refl _, ?_⟩
  intro x y
  simp only [sub_self, abs_zero, zero_mul, le_refl]

end LatticeProb.Percolation

import LatticeProb.Network.IntegerLaplacianSupport

/-!
# A fractional potential with integer poles

On an infinite graph consisting of a triangle and isolated vertices, the potential
`(2/3, -1/3, -1/3, 0, ...)` has negative Laplacian `(2, -1, -1, 0, ...)`.
This supplies a finite-support rational-valued example with nonzero integer poles,
while the potential itself is not integer-valued.
-/

namespace LatticeProb.Network.FiniteTriangle

open Filter
open scoped Topology

/-- The triangle on vertices zero, one and two, with all other natural vertices isolated. -/
def graph : SimpleGraph ℕ where
  Adj m n := m ≠ n ∧ m < 3 ∧ n < 3
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Each neighbor set is contained in the three vertices of the triangle. -/
noncomputable instance graphLocallyFinite : graph.LocallyFinite := fun _ =>
  ((Finset.range 3).finite_toSet.subset (by
    intro n hn
    exact Finset.mem_range.mpr hn.2.2)).fintype

/-- The graph has uniformly bounded degree, including at its infinitely many isolated vertices. -/
theorem degree_le (n : ℕ) : graph.degree n ≤ 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : graph.neighborFinset n ⊆ Finset.range 3 := by
    intro m hm
    exact Finset.mem_range.mpr ((SimpleGraph.mem_neighborFinset graph n m).mp hm).2.2
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range 3)

/-- The three neighbor sets within the triangle are explicit. -/
theorem neighborFinset_small :
    graph.neighborFinset 0 = {1, 2} ∧ graph.neighborFinset 1 = {0, 2} ∧
      graph.neighborFinset 2 = {0, 1} := by
  constructor
  · ext n
    simp only [SimpleGraph.mem_neighborFinset, graph, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  constructor
  · ext n
    simp only [SimpleGraph.mem_neighborFinset, graph, Finset.mem_insert,
      Finset.mem_singleton]
    omega
  · ext n
    simp only [SimpleGraph.mem_neighborFinset, graph, Finset.mem_insert,
      Finset.mem_singleton]
    omega

/-- Vertices beyond the triangle are isolated. -/
theorem neighborFinset_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    graph.neighborFinset n = ∅ := by
  ext m
  simp only [SimpleGraph.mem_neighborFinset, graph, Finset.notMem_empty, iff_false]
  omega

/-- The rational-valued potential on the triangle, extended by zero to the infinite graph. -/
noncomputable def potential (n : ℕ) : ℝ :=
  if n = 0 then 2 / 3 else if n < 3 then -(1 / 3) else 0

/-- The negative Laplacian has the integer pole values two, minus one and minus one. -/
def pole (n : ℕ) : ℤ := if n = 0 then 2 else if n < 3 then -1 else 0

/-- The potential is rational-valued at every vertex. -/
theorem potential_rational (n : ℕ) : ∃ q : ℚ, potential n = (q : ℝ) := by
  unfold potential
  split_ifs
  · exact ⟨2 / 3, by norm_num⟩
  · exact ⟨-(1 / 3), by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- This example does not satisfy an integer-value assumption on the potential. -/
theorem potential_zero_not_integer : ¬ ∃ z : ℤ, potential 0 = (z : ℝ) := by
  rintro ⟨z, hz⟩
  have hpos : (0 : ℝ) < z := by rw [← hz]; norm_num [potential]
  have hlt : (z : ℝ) < 1 := by rw [← hz]; norm_num [potential]
  have : (0 : ℤ) < z := by exact_mod_cast hpos
  have : z < (1 : ℤ) := by exact_mod_cast hlt
  omega

/-- The potential itself has finite support contained in the triangle. -/
theorem potential_hasFiniteSupport : Function.HasFiniteSupport potential := by
  refine (Finset.range 3).finite_toSet.subset ?_
  intro n hn
  by_contra hout
  have hn3 : ¬ n < 3 := by simpa only [Finset.mem_coe, Finset.mem_range] using hout
  have hn0 : n ≠ 0 := by omega
  exact hn (by simp only [potential, if_neg hn0, if_neg hn3])

/-- The potential tends to zero along the cofinite filter of the infinite vertex type. -/
theorem potential_tendsto_zero : Tendsto potential cofinite (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(Finset.range 3).eventually_cofinite_notMem] with n hn
  have hn3 : ¬ n < 3 := by simpa only [Finset.mem_range] using hn
  have hn0 : n ≠ 0 := by omega
  simp only [potential, if_neg hn0, if_neg hn3]

/-- Direct evaluation verifies the Poisson equation at every vertex. -/
theorem neg_netLaplacian_eq_pole (n : ℕ) :
    -netLaplacian graph (unitCond graph) potential n = (pole n : ℝ) := by
  rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian]
  rcases lt_or_ge n 3 with hn | hn
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · rw [neighborFinset_small.1]
      norm_num [potential, pole]
    · rw [neighborFinset_small.2.1]
      norm_num [potential, pole]
    · rw [neighborFinset_small.2.2]
      norm_num [potential, pole]
  · rw [neighborFinset_of_three_le n hn]
    have hn0 : n ≠ 0 := by omega
    simp only [Finset.sum_empty, neg_zero, pole, if_neg hn0, if_neg (not_lt.mpr hn),
      Int.cast_zero]

/-- The finite-pole producer applies with every premise discharged for the example. -/
theorem pole_hasFiniteSupport : Function.HasFiniteSupport pole :=
  finite_support_pole_of_tendsto_zero 3 degree_le potential potential_tendsto_zero pole
    neg_netLaplacian_eq_pole

/-- The pole support consists of exactly the triangle; in particular it is nonempty. -/
theorem support_pole : Function.support pole = ({0, 1, 2} : Set ℕ) := by
  ext n
  simp only [Function.mem_support, pole, Set.mem_insert_iff, Set.mem_singleton_iff]
  split_ifs <;> omega

end LatticeProb.Network.FiniteTriangle

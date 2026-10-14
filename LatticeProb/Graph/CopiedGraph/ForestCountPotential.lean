/- The literal forest-count potential, normalized by the original tree count.
Averaging copied tree-path conservation yields its positive Poisson equation. -/
import LatticeProb.Graph.CopiedGraph.TreeCutCount
import LatticeProb.Graph.CopiedGraph.TreeExistence
import LatticeProb.Graph.CopiedGraph.PathDivergence
import Mathlib.Algebra.BigOperators.Field

namespace LatticeProb.Graph.CopiedGraph
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*}

/-- No forest rooted at distinct vertices connects the second root to the first. -/
theorem forestColorCount_ground (J : CopiedGraph V E) (u v : V) (hu : u ≠ v) :
    forestColorCount J u v v = 0 := by
  apply Nat.card_eq_zero.mpr
  exact Or.inl ⟨fun F =>
    twoRootForest_roots_separated J u v hu F.val (J.reaches_symm F.property)⟩

variable [Fintype E]

/-- The positive copied Laplacian, summing the two endpoint incidences of each
original copy. Both incidences of a loop vanish; parallel IDs remain separate. -/
def positiveLaplacian (J : CopiedGraph V E) (f : V → ℝ) (x : V) : ℝ :=
  ∑ e, ((if J.left e = x then f x - f (J.right e) else 0) +
    (if J.right e = x then f x - f (J.left e) else 0))

/-- The positive copied Laplacian is the divergence of stored endpoint differences. -/
theorem positiveLaplacian_eq_incidence (J : CopiedGraph V E) (f : V → ℝ) (x : V) :
    positiveLaplacian J f x =
      ∑ e, ((if J.left e = x then f (J.left e) - f (J.right e) else 0) -
        (if J.right e = x then f (J.left e) - f (J.right e) else 0)) := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : J.left e = x <;> by_cases hr : J.right e = x <;>
    simp [hl, hr, neg_sub]

/-- Dividing a potential by a constant divides its positive Laplacian by the same constant. -/
theorem positiveLaplacian_div (J : CopiedGraph V E) (f : V → ℝ) (c : ℝ) (x : V) :
    positiveLaplacian J (fun y => f y / c) x = positiveLaplacian J f x / c := by
  rw [positiveLaplacian_eq_incidence, positiveLaplacian_eq_incidence, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : J.left e = x <;> by_cases hr : J.right e = x <;>
    simp [hl, hr, sub_div]

/-- The unnormalized count potential has source-minus-ground Laplacian equal to
one unit for every original spanning tree, without a connectivity assumption. -/
theorem positiveLaplacian_forestColorCount (J : CopiedGraph V E)
    (u v : V) (hu : u ≠ v) (x : V) :
    positiveLaplacian J (fun y => (forestColorCount J u v y : ℝ)) x =
      (Fintype.card J.SpanningTree : ℝ) *
        ((if x = u then (1 : ℝ) else 0) - (if x = v then (1 : ℝ) else 0)) := by
  rw [positiveLaplacian_eq_incidence]
  calc
    _ = ∑ e : E,
        ((if J.left e = x then ∑ T : J.SpanningTree, J.signedPathTraversal T u v e else 0) -
          (if J.right e = x then ∑ T : J.SpanningTree, J.signedPathTraversal T u v e else 0)) := by
      simp_rw [sum_signedPathTraversal_eq_count_sub J u v hu]
    _ = ∑ e : E, ∑ T : J.SpanningTree,
        ((if J.left e = x then J.signedPathTraversal T u v e else 0) -
          (if J.right e = x then J.signedPathTraversal T u v e else 0)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero]
    _ = ∑ T : J.SpanningTree, ∑ e : E,
        ((if J.left e = x then J.signedPathTraversal T u v e else 0) -
          (if J.right e = x then J.signedPathTraversal T u v e else 0)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [signedPathTraversal_divergence, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The literal first-root forest count divided by the original spanning-tree count.
It is a full-carrier quotient, not a voltage chosen by an unproved characterization. -/
def forestCountPotential (J : CopiedGraph V E) (u v x : V) : ℝ :=
  (forestColorCount J u v x : ℝ) / (Fintype.card J.SpanningTree : ℝ)

/-- The count potential vanishes at the second root when the roots are distinct. -/
theorem forestCountPotential_ground (J : CopiedGraph V E) (u v : V) (hu : u ≠ v) :
    forestCountPotential J u v v = 0 := by
  rw [forestCountPotential, forestColorCount_ground J u v hu]
  simp

/-- On a connected copied graph the count potential has exactly unit injection
at the first root and unit extraction at the second root. Tree-count positivity
is derived from connectivity on the full original carrier. -/
theorem positiveLaplacian_forestCountPotential (J : CopiedGraph V E)
    (u v : V) (hu : u ≠ v) (hconn : ∀ a b : V, J.reaches Finset.univ a b) (x : V) :
    positiveLaplacian J (forestCountPotential J u v) x =
      (if x = u then (1 : ℝ) else 0) - (if x = v then (1 : ℝ) else 0) := by
  letI : Nonempty V := ⟨v⟩
  have hcard : (Fintype.card J.SpanningTree : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (J.card_spanningTree_pos hconn))
  change positiveLaplacian J
    (fun y => (forestColorCount J u v y : ℝ) / (Fintype.card J.SpanningTree : ℝ)) x = _
  rw [positiveLaplacian_div, positiveLaplacian_forestColorCount J u v hu]
  exact mul_div_cancel_left₀ _ hcard

/-- The literal count potential satisfies the zero-ground Poisson specification
on a connected copied graph, with no assumed solver or determinant identity. -/
theorem forestCountPotential_poisson (J : CopiedGraph V E) (u v : V) (hu : u ≠ v)
    (hconn : ∀ a b : V, J.reaches Finset.univ a b) :
    forestCountPotential J u v v = 0 ∧
      ∀ x, x ≠ v → positiveLaplacian J (forestCountPotential J u v) x =
        if x = u then (1 : ℝ) else 0 := by
  refine ⟨forestCountPotential_ground J u v hu, ?_⟩
  intro x hx
  rw [positiveLaplacian_forestCountPotential J u v hu hconn, if_neg hx, sub_zero]

/-- The averaged signed traversal is the stored endpoint drop of the literal
forest-count potential, with the same original tree-count normalization. -/
theorem mean_signedPathTraversal_eq_potential_drop (J : CopiedGraph V E)
    (u v : V) (hu : u ≠ v) (e : E) :
    (∑ T : J.SpanningTree, J.signedPathTraversal T u v e) /
        (Fintype.card J.SpanningTree : ℝ) =
      forestCountPotential J u v (J.left e) - forestCountPotential J u v (J.right e) := by
  rw [sum_signedPathTraversal_eq_count_sub J u v hu, sub_div]
  rfl

end
end LatticeProb.Graph.CopiedGraph

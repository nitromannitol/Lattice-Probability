import LatticeProb.Network.Variational
import Mathlib.Order.Filter.Cofinite

/-!
# Finite pole support from decay and integer Laplacian

For a locally finite simple graph with uniformly bounded degree, a real function tending
 to zero along the cofinite filter has finite Laplacian support whenever its unit network
Laplacian is integer-valued. The proof enlarges a finite exceptional set by its neighbors
and uses the discreteness of the integers. The function itself need not be integer-valued.
-/

namespace LatticeProb.Network

open Filter
open scoped Topology

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- Small values at a vertex and all its neighbors bound its unit network Laplacian. -/
theorem abs_netLaplacian_unitCond_le (u : V → ℝ) (x : V) (ε : ℝ)
    (hx : |u x| ≤ ε) (hn : ∀ y, G.Adj x y → |u y| ≤ ε) :
    |netLaplacian G (unitCond G) u x| ≤ (G.degree x : ℝ) * (2 * ε) := by
  classical
  rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian]
  calc
    |∑ y ∈ G.neighborFinset x, (u y - u x)|
        ≤ ∑ y ∈ G.neighborFinset x, |u y - u x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ G.neighborFinset x, (2 * ε) := by
      apply Finset.sum_le_sum
      intro y hy
      have hybound := hn y ((SimpleGraph.mem_neighborFinset G x y).mp hy)
      exact (abs_sub (u y) (u x)).trans (by linarith)
    _ = (G.degree x : ℝ) * (2 * ε) := by
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]

/-- Decay and an integer-valued unit Laplacian force finite Laplacian support.
The degree bound may be zero; the threshold uses `N + 1`. -/
theorem finite_support_netLaplacian_unitCond_of_tendsto_zero (N : ℕ)
    (hdegree : ∀ x, G.degree x ≤ N) (u : V → ℝ)
    (hdecay : Tendsto u cofinite (𝓝 0))
    (hinteger : ∀ x, ∃ z : ℤ, netLaplacian G (unitCond G) u x = (z : ℝ)) :
    (Function.support (netLaplacian G (unitCond G) u)).Finite := by
  classical
  let ε : ℝ := 1 / (2 * ((N : ℝ) + 1))
  have hN : 0 < (N : ℝ) + 1 := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hevent : ∀ᶠ x in cofinite, |u x| < ε := by
    simpa only [Real.dist_eq, sub_zero] using (Metric.tendsto_nhds.mp hdecay ε hε)
  have hfinite := eventually_cofinite.mp hevent
  let C : Finset V := hfinite.toFinset
  have hsmall (x : V) (hx : x ∉ C) : |u x| ≤ ε := by
    have hnot : ¬ ¬ |u x| < ε := by
      simpa only [C, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hx
    exact (not_not.mp hnot).le
  refine (nbhd G C).finite_toSet.subset ?_
  intro x hx
  by_contra hout
  have hxC : x ∉ C := fun h => hout (subset_nbhd C h)
  have hn (y : V) (hxy : G.Adj x y) : |u y| ≤ ε := by
    apply hsmall y
    intro hy
    exact hout (mem_nbhd_of_adj hy hxy.symm)
  have hbound := abs_netLaplacian_unitCond_le u x ε (hsmall x hxC) hn
  have hd : (G.degree x : ℝ) ≤ N := by exact_mod_cast hdegree x
  have hthreshold : (N : ℝ) * (2 * ε) < 1 := by
    dsimp [ε]
    field_simp
    nlinarith
  have habs : |netLaplacian G (unitCond G) u x| < 1 :=
    (hbound.trans (mul_le_mul_of_nonneg_right hd (by positivity))).trans_lt hthreshold
  obtain ⟨z, hz⟩ := hinteger x
  have hzabs : |z| < (1 : ℤ) := by
    rw [hz] at habs
    exact_mod_cast habs
  have hz0 := Int.abs_lt_one_iff.mp hzabs
  exact hx (by rw [hz, hz0, Int.cast_zero])

/-- Integer values of the positive and negative unit Laplacians are equivalent. -/
theorem netLaplacian_integer_iff_neg (u : V → ℝ) :
    (∀ x, ∃ z : ℤ, netLaplacian G (unitCond G) u x = (z : ℝ)) ↔
      (∀ x, ∃ z : ℤ, -netLaplacian G (unitCond G) u x = (z : ℝ)) := by
  constructor
  · intro h x
    obtain ⟨z, hz⟩ := h x
    exact ⟨-z, by rw [hz, Int.cast_neg]⟩
  · intro h x
    obtain ⟨z, hz⟩ := h x
    refine ⟨-z, ?_⟩
    rw [Int.cast_neg, ← hz, neg_neg]

/-- A decaying real solution of the integer Poisson equation has a finitely supported pole. -/
theorem finite_support_pole_of_tendsto_zero (N : ℕ) (hdegree : ∀ x, G.degree x ≤ N)
    (u : V → ℝ) (hdecay : Tendsto u cofinite (𝓝 0)) (f : V → ℤ)
    (hpoisson : ∀ x, -netLaplacian G (unitCond G) u x = (f x : ℝ)) :
    Function.HasFiniteSupport f := by
  have hi := (netLaplacian_integer_iff_neg u).mpr (fun x => ⟨f x, hpoisson x⟩)
  refine (finite_support_netLaplacian_unitCond_of_tendsto_zero N hdegree u hdecay hi).subset ?_
  intro x hx hzero
  have hcast : (f x : ℝ) = 0 := by rw [← hpoisson x, hzero, neg_zero]
  exact hx (Int.cast_eq_zero.mp hcast)

/-- A decaying function with integer unit Laplacian is harmonic outside a finite set. -/
theorem harmonicOn_compl_finset_of_tendsto_zero (N : ℕ) (hdegree : ∀ x, G.degree x ≤ N)
    (u : V → ℝ) (hdecay : Tendsto u cofinite (𝓝 0))
    (hinteger : ∀ x, ∃ z : ℤ, netLaplacian G (unitCond G) u x = (z : ℝ)) :
    ∃ C : Finset V, HarmonicOn G (unitCond G) u (C : Set V)ᶜ := by
  classical
  have hfinite := finite_support_netLaplacian_unitCond_of_tendsto_zero
    N hdegree u hdecay hinteger
  refine ⟨hfinite.toFinset, ?_⟩
  intro x hx
  have hnot : x ∉ Function.support (netLaplacian G (unitCond G) u) := by
    simpa only [Set.mem_compl_iff, Finset.mem_coe, Set.Finite.mem_toFinset] using hx
  exact not_not.mp hnot

end LatticeProb.Network

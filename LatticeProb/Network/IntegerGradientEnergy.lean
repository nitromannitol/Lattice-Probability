import LatticeProb.Network.FiniteDeletionComponents
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Finite energy with integer gradients

Uniformly bounded finite partial sums of squared integer gradients force finite edge support.
Sums use ordered adjacent pairs, so each unoriented edge contributes twice to the full energy.
After deleting exactly the nonzero-gradient edges, a unique infinite component gives constancy
outside a finite vertex set. No harmonicity, countability or local finiteness is required.
-/

namespace LatticeProb.Network

open SimpleGraph
open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V} {u : V → ℝ}

/-- Bounded finite partial energy sums and integer gradients imply finite ordered support. -/
theorem finite_nonzero_ordered_gradients
    (hint : ∀ x y, G.Adj x y → ∃ z : ℤ, u x - u y = (z : ℝ))
    (henergy : ∃ K : ℝ, ∀ F : Finset (V × V),
      (∀ e ∈ F, G.Adj e.1 e.2) → ∑ e ∈ F, (u e.1 - u e.2) ^ 2 ≤ K) :
    {e : V × V | G.Adj e.1 e.2 ∧ u e.1 ≠ u e.2}.Finite := by
  classical
  obtain ⟨K, hK⟩ := henergy
  by_contra hinf
  obtain ⟨n, hn⟩ := exists_nat_gt K
  obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have hlower : (F.card : ℝ) ≤ ∑ e ∈ F, (u e.1 - u e.2) ^ 2 := by
    calc
      (F.card : ℝ) = ∑ _e ∈ F, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ e ∈ F, (u e.1 - u e.2) ^ 2 := by
        apply Finset.sum_le_sum
        intro e he
        obtain ⟨z, hz⟩ := hint e.1 e.2 (hF he).1
        have hz0 : z ≠ 0 := by
          intro hzero
          exact (hF he).2 (sub_eq_zero.mp (by simpa only [hzero, Int.cast_zero] using hz))
        have hzbound : z ≤ -1 ∨ 1 ≤ z := by omega
        rw [hz]
        rcases hzbound with hneg | hpos
        · have h : (z : ℝ) ≤ -1 := by exact_mod_cast hneg
          nlinarith
        · have h : (1 : ℝ) ≤ z := by exact_mod_cast hpos
          nlinarith
  have hupper := hK F (fun e he => (hF he).1)
  rw [hcard] at hlower
  exact (not_le_of_gt hn) (hlower.trans hupper)

/-- The exact unordered set of adjacent pairs with unequal values is finite. -/
theorem finite_nonzero_gradient_edges
    (hint : ∀ x y, G.Adj x y → ∃ z : ℤ, u x - u y = (z : ℝ))
    (henergy : ∃ K : ℝ, ∀ F : Finset (V × V),
      (∀ e ∈ F, G.Adj e.1 e.2) → ∑ e ∈ F, (u e.1 - u e.2) ^ 2 ≤ K) :
    {e : Sym2 V | ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ u x ≠ u y}.Finite := by
  have hfinite := (finite_nonzero_ordered_gradients hint henergy).image
    (fun e : V × V => s(e.1, e.2))
  apply hfinite.subset
  rintro e ⟨x, y, rfl, hxy, hne⟩
  exact ⟨(x, y), ⟨hxy, hne⟩, rfl⟩

/-- Deleting exactly the nonzero-gradient edges makes the function constant on each
connected component, by induction along an actual walk. -/
theorem eq_of_mem_nonzero_gradient_deleted_component
    (C : (G.deleteEdges
      {e : Sym2 V | ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ u x ≠ u y}).ConnectedComponent)
    {x y : V} (hx : x ∈ C.supp) (hy : y ∈ C.supp) : u x = u y := by
  have hreach := ConnectedComponent.exact
    (((ConnectedComponent.mem_supp_iff C x).mp hx).trans
      ((ConnectedComponent.mem_supp_iff C y).mp hy).symm)
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    have hab' := deleteEdges_adj.mp hab
    have heq : u a = u b := by
      by_contra hne
      exact hab'.2 ⟨a, b, rfl, hab'.1, hne⟩
    exact heq.trans (ih ((C.mem_supp_congr_adj hab).mp hx) hy)

/-- On a connected graph, finite integer-gradient energy and a unique infinite component
of the exact gradient-edge deletion give constancy outside a finite vertex set. -/
theorem exists_finite_exception_constant_of_integer_gradient_energy
    (hG : G.Connected)
    (hint : ∀ x y, G.Adj x y → ∃ z : ℤ, u x - u y = (z : ℝ))
    (henergy : ∃ K : ℝ, ∀ F : Finset (V × V),
      (∀ e ∈ F, G.Adj e.1 e.2) → ∑ e ∈ F, (u e.1 - u e.2) ^ 2 ≤ K)
    (K : (G.deleteEdges
      {e : Sym2 V | ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ u x ≠ u y}).ConnectedComponent)
    (hK : K.supp.Infinite)
    (hunique : ∀ C : (G.deleteEdges
      {e : Sym2 V | ∃ x y, e = s(x, y) ∧ G.Adj x y ∧ u x ≠ u y}).ConnectedComponent,
      C.supp.Infinite → C = K) :
    ∃ S : Set V, S.Finite ∧ ∃ c : ℝ, ∀ x, x ∉ S → u x = c := by
  obtain ⟨y, hy⟩ := K.nonempty_supp
  refine ⟨K.suppᶜ, finite_compl_of_unique_infinite_component hG
    (finite_nonzero_gradient_edges hint henergy) K hK hunique, u y, ?_⟩
  intro x hx
  exact eq_of_mem_nonzero_gradient_deleted_component K (Classical.not_not.mp hx) hy

end LatticeProb.Network

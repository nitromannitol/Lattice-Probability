import LatticeProb.Network.FiniteEdgeRemoval
import LatticeProb.Network.Variational

/-!
# Single-edge cancellation under a cofinite difference hypothesis

Two harmonic functions on a graph and its single-edge deletion have zero old edge drop
if their difference is constant outside a finite set. All pairings are finite; the
ordered-edge energy retains its factor two. No connectivity assumption is needed.
-/

open scoped BigOperators Classical

namespace LatticeProb.Network

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-- Removing one adjacent edge changes the Laplacian by its two signed endpoint drops. -/
theorem netLaplacian_single_edge_difference {a b : V} (hab : G.Adj a b)
    (f : V → ℝ) (x : V) :
    netLaplacian G (unitCond G) f x -
      netLaplacian (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V)))
        (unitCond (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V)))) f x =
      (if x = a then f b - f a else 0) + (if x = b then f a - f b else 0) := by
  classical
  rw [netLaplacian_sub_deleteEdges G {s(a, b)} f x]
  have hne := hab.ne
  by_cases ha : x = a
  · subst x
    have hr : removedNeighbors G {s(a, b)} a = {b} := by
      ext y
      simp only [removedNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        Finset.mem_singleton, Sym2.eq_iff]
      constructor
      · rintro ⟨_, h | h⟩
        · exact h.2
        · exact (hne h.1).elim
      · intro h
        subst y
        exact ⟨hab, Or.inl ⟨True.intro, rfl⟩⟩
    simp only [hr, Finset.sum_singleton, ite_true, if_neg hne, add_zero]
  · by_cases hb : x = b
    · subst x
      have hr : removedNeighbors G {s(a, b)} b = {a} := by
        ext y
        simp only [removedNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
          Finset.mem_singleton, Sym2.eq_iff]
        constructor
        · rintro ⟨_, h | h⟩
          · exact (ha h.1).elim
          · exact h.2
        · intro h
          subst y
          exact ⟨hab.symm, Or.inr ⟨True.intro, rfl⟩⟩
      simp only [hr, Finset.sum_singleton, if_neg ha, ite_true, zero_add]
    · have hr : removedNeighbors G {s(a, b)} x = ∅ := by
        ext y
        simp only [removedNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
          Finset.mem_singleton, Sym2.eq_iff, Finset.notMem_empty, iff_false, not_and]
        intro _ h
        rcases h with h | h
        · exact ha h.1
        · exact hb h.1
      simp only [hr, Finset.sum_empty, if_neg ha, if_neg hb, add_zero]

/-- A compactly supported function pairs to zero with a globally harmonic function.
The harmonic function is truncated on a neighborhood before finite summation by parts. -/
theorem sum_mul_laplacian_eq_zero_of_compact_harmonic (u w : V → ℝ) (B : Finset V)
    (hw : ∀ x, x ∉ B → w x = 0)
    (hu : ∀ x, netLaplacian G (unitCond G) u x = 0) :
    ∑ x ∈ nbhd G B, u x * netLaplacian G (unitCond G) w x = 0 := by
  classical
  let S := nbhd G B
  let T := nbhd G S
  let U : V → ℝ := fun x => if x ∈ S then u x else 0
  have hU : ∀ x, x ∉ S → U x = 0 := by
    intro x hx
    exact if_neg hx
  have hUL : ∀ x ∈ B, netLaplacian G (unitCond G) U x = 0 := by
    intro x hx
    rw [netLaplacian, ← hu x, netLaplacian]
    apply Finset.sum_congr rfl
    intro y hy
    have hxS : x ∈ S := subset_nbhd B hx
    have hyS : y ∈ S := mem_nbhd_of_adj hx ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
    simp only [U, if_pos hxS, if_pos hyS]
  have hleft := formOn_eq_neg_two_mul (isCond_unitCond (G := G)) T B U w hw
    (fun x hx => subset_nbhd S (subset_nbhd B hx))
    (fun x hx y hxy => subset_nbhd S (mem_nbhd_of_adj hx hxy))
  have hright := formOn_eq_neg_two_mul (isCond_unitCond (G := G)) T S w U hU
    (subset_nbhd S) (fun _ hx _ hxy => mem_nbhd_of_adj hx hxy)
  have hz : formOn G (unitCond G) T U w = 0 := by
    rw [hleft]
    have hzsum : (∑ x ∈ B, w x * netLaplacian G (unitCond G) U x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [hUL x hx, mul_zero]
    rw [hzsum, mul_zero]
  rw [formOn_comm] at hz
  rw [hright] at hz
  have hs : (∑ x ∈ S, U x * netLaplacian G (unitCond G) w x) =
      ∑ x ∈ S, u x * netLaplacian G (unitCond G) w x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [U, if_pos hx]
  rw [hs] at hz
  linarith

/-- Conditional generic cancellation: harmonic functions on the original and deleted
single-edge graphs whose difference is cofinally constant have zero original edge drop. -/
theorem edge_drop_eq_zero_of_harmonic_cofinite_difference {a b : V} (hab : G.Adj a b)
    (u v : V → ℝ)
    (hu : ∀ x, netLaplacian G (unitCond G) u x = 0)
    (hv : ∀ x, netLaplacian (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V)))
      (unitCond (G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V)))) v x = 0)
    (hcof : ∃ (K : Finset V) (c : ℝ), ∀ x, x ∉ K → v x - u x = c) : u a = u b := by
  classical
  obtain ⟨K, c, hc⟩ := hcof
  let D := G.deleteEdges (({s(a, b)} : Finset (Sym2 V)) : Set (Sym2 V))
  let B := K ∪ {a, b}
  let w : V → ℝ := fun x => (v x - u x) - c
  have hw : ∀ x, x ∉ B → w x = 0 := by
    intro x hx
    have hxK : x ∉ K := fun h => hx (Finset.mem_union_left _ h)
    exact sub_eq_zero.mpr (hc x hxK)
  have ha : a ∈ B := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hb : b ∈ B := Finset.mem_union_right _ (Finset.mem_insert_of_mem (by simp only
    [Finset.mem_singleton]))
  have hG : ∀ x, netLaplacian G (unitCond G) w x =
      (if x = a then v b - v a else 0) + (if x = b then v a - v b else 0) := by
    intro x
    have hd := netLaplacian_single_edge_difference G hab v x
    dsimp only [w]
    rw [netLaplacian_sub, netLaplacian_sub, netLaplacian_const, hu, sub_zero, sub_zero]
    rw [hv, sub_zero] at hd
    exact hd
  have hD : ∀ x, netLaplacian D (unitCond D) w x =
      (if x = a then u b - u a else 0) + (if x = b then u a - u b else 0) := by
    intro x
    have hd := netLaplacian_single_edge_difference G hab u x
    rw [hu, zero_sub] at hd
    dsimp only [w]
    rw [netLaplacian_sub, netLaplacian_sub, netLaplacian_const, hv, sub_zero, zero_sub]
    exact hd
  have hpair := sum_mul_laplacian_eq_zero_of_compact_harmonic G u w B hw hu
  simp_rw [hG, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero] at hpair
  simp only [Finset.sum_ite_eq', if_pos (subset_nbhd B ha),
    if_pos (subset_nbhd B hb)] at hpair
  have hen := energyOn_nonneg (isCond_unitCond (G := D)) (nbhd G B) w
  rw [energyOn_eq_neg_two_mul (isCond_unitCond (G := D)) (nbhd G B) B w hw
    (subset_nbhd B) (fun _ hx _ hxy =>
      mem_nbhd_of_adj hx (SimpleGraph.deleteEdges_adj.mp hxy).1)] at hen
  simp_rw [hD, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero] at hen
  simp only [Finset.sum_ite_eq', if_pos ha, if_pos hb] at hen
  dsimp only [w, Pi.sub_apply] at hen
  nlinarith [sq_nonneg (u a - u b)]

end LatticeProb.Network

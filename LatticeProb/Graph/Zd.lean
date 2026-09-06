/-
The specialization of the general-graph setting to the nearest-neighbour
lattice `ℤ^d` of the shared library, in the vocabulary the dependent
formalizations use: the graph is `LatticeProb.lattice d`, every vertex has
degree `2d`, and the averaging operator is `LatticeProb.walkOp`.
-/
import LatticeProb.Graph.HeatBasic
import LatticeProb.Graph.Green
import LatticeProb.Site

namespace LatticeProb.Graph.Zd

open LatticeProb

variable {d : ℕ}

theorem mem_nbrFinset {x y : Site d} :
    y ∈ nbrFinset x ↔ ∃ i : Fin d, y = x + unit i ∨ y = x - unit i := by
  simp [nbrFinset]

theorem adj_iff {x y : Site d} :
    (lattice d).Adj x y ↔ ∃ i : Fin d, y = x + unit i ∨ y = x - unit i := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩

theorem neighborSet_eq (x : Site d) :
    (lattice d).neighborSet x = ↑(nbrFinset x) := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, Finset.mem_coe, mem_nbrFinset]
  exact adj_iff

noncomputable instance latticeLocallyFinite (d : ℕ) : (lattice d).LocallyFinite := fun x =>
  Set.Finite.fintype (by rw [neighborSet_eq]; exact (nbrFinset x).finite_toSet)

theorem neighborFinset_eq (x : Site d) :
    (lattice d).neighborFinset x = nbrFinset x := by
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  exact adj_iff.trans mem_nbrFinset.symm

theorem card_nbrFinset (x : Site d) : (nbrFinset x).card = 2 * d := by
  classical
  rw [nbrFinset, Finset.card_biUnion]
  · have : ∀ i : Fin d, ({x + unit i, x - unit i} : Finset (Site d)).card = 2 := by
      intro i
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      intro h
      have := congrFun h i
      simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
      omega
    simp [this, Finset.sum_const, mul_comm]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

theorem degree_eq (x : Site d) : (lattice d).degree x = 2 * d := by
  rw [SimpleGraph.degree, neighborFinset_eq, card_nbrFinset]

theorem walkOp_eq (f : Site d → ℝ) (x : Site d) :
    LatticeProb.Graph.walkOp (lattice d) f x = LatticeProb.walkOp f x := by
  classical
  rw [LatticeProb.Graph.walkOp, LatticeProb.walkOp, degree_eq, neighborFinset_eq, LatticeProb.nbrSum,
    nbrFinset, Finset.sum_biUnion]
  · rw [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) from by push_cast; ring]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_insert, Finset.sum_singleton]
    simp only [Finset.mem_singleton]
    intro h
    have := congrFun h i
    simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
    omega
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-! ### The lattice is infinite and connected -/

instance latticeInfinite (d : ℕ) [NeZero d] : Infinite (Site d) :=
  Infinite.of_injective (fun n : ℤ => (Pi.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ n : Site d))
    (fun a b h => by
      have := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
      simpa using this)

theorem reachable_add_zsmul (x : Site d) (i : Fin d) (k : ℤ) :
    (lattice d).Reachable x (x + k • unit i) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      refine adj_iff.mpr ⟨i, Or.inl ?_⟩
      module
  | pred n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      refine adj_iff.mpr ⟨i, Or.inr ?_⟩
      module

theorem reachable_add_sum (x : Site d) (c : Fin d → ℤ) (s : Finset (Fin d)) :
    (lattice d).Reachable x (x + ∑ i ∈ s, c i • unit i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi,
        show x + (c i • unit i + ∑ j ∈ s, c j • unit j)
          = (x + ∑ j ∈ s, c j • unit j) + c i • unit i from by abel]
      exact ih.trans (reachable_add_zsmul _ i _)

theorem latticeConnected (d : ℕ) [NeZero d] : (lattice d).Connected := by
  classical
  have hpre : ∀ x y : Site d, (lattice d).Reachable x y := by
    intro x y
    have hy : y = x + ∑ i : Fin d, (y i - x i) • unit i := by
      funext j
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, unit, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j (fun i => y i - x i)]
      simp
    rw [hy]
    exact reachable_add_sum x _ _
  exact ⟨hpre⟩

end LatticeProb.Graph.Zd

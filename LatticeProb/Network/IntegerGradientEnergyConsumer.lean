import LatticeProb.Network.IntegerGradientEnergy
import LatticeProb.Network.FiniteDeletionComponentsConsumer

/-!
# Consumers of finite integer-gradient energy

Constant real functions on the infinite ray discharge every hypothesis of the cofinite
constancy theorem using the proved unique infinite component after empty deletion.
A two-vertex complete graph supplies integer-gradient examples with genuinely positive energy.
-/

namespace LatticeProb.Network

open SimpleGraph
open scoped BigOperators

/-- Every constant real function on the infinite ray satisfies the generic cofinite
constancy conclusion, with the actual empty-deletion unique infinite component. -/
theorem constant_ray_finite_exceptions (c : ℝ) :
    ∃ S : Set ℕ, S.Finite ∧ ∃ a : ℝ, ∀ x, x ∉ S → (fun _ : ℕ => c) x = a := by
  have hB : {e : Sym2 ℕ | ∃ x y, e = s(x, y) ∧ Ray.graph.Adj x y ∧ c ≠ c} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, ne_self_iff_false, and_false, exists_false,
      Set.mem_empty_iff_false]
  have hcomponent : ∃! K : (Ray.graph.deleteEdges
      {e : Sym2 ℕ | ∃ x y, e = s(x, y) ∧ Ray.graph.Adj x y ∧ c ≠ c}).ConnectedComponent,
      K.supp.Infinite := by
    rw [hB]
    exact Ray.empty_deletion_unique_infinite
  obtain ⟨K, hK, hunique⟩ := hcomponent
  apply exists_finite_exception_constant_of_integer_gradient_energy Ray.graph_connected
    (u := fun _ => c) (fun _ _ _ => ⟨0, by simp only [sub_self, Int.cast_zero]⟩)
    ?_ K hK (fun C hC => hunique C hC)
  refine ⟨0, ?_⟩
  intro F _
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, le_refl]

/-- On the two-vertex complete graph, the values zero and an arbitrary integer have
integer gradients and ordered finite partial energy bounded by twice its square. -/
theorem two_vertex_integer_energy (z : ℤ) :
    (∀ x y : Bool, (⊤ : SimpleGraph Bool).Adj x y →
      ∃ k : ℤ, (if x then (z : ℝ) else 0) - (if y then (z : ℝ) else 0) = (k : ℝ)) ∧
    (∃ K : ℝ, ∀ F : Finset (Bool × Bool),
      (∀ e ∈ F, (⊤ : SimpleGraph Bool).Adj e.1 e.2) →
      ∑ e ∈ F, ((if e.1 then (z : ℝ) else 0) -
        (if e.2 then (z : ℝ) else 0)) ^ 2 ≤ K) := by
  constructor
  · intro x y _
    cases x <;> cases y
    · exact ⟨0, by simp only [Bool.false_eq_true, ↓reduceIte, sub_self, Int.cast_zero]⟩
    · exact ⟨-z, by simp only [Bool.false_eq_true, ↓reduceIte, zero_sub, Int.cast_neg]⟩
    · exact ⟨z, by simp only [Bool.false_eq_true, ↓reduceIte, sub_zero]⟩
    · exact ⟨0, by simp only [↓reduceIte, sub_self, Int.cast_zero]⟩
  · refine ⟨2 * (z : ℝ) ^ 2, ?_⟩
    intro F _
    calc
      _ ≤ ∑ e : Bool × Bool, ((if e.1 then (z : ℝ) else 0) -
          (if e.2 then (z : ℝ) else 0)) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
          (fun _ _ _ => sq_nonneg _)
      _ = 2 * (z : ℝ) ^ 2 := by
        simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
          ↓reduceIte, sub_self,
          zero_pow (by decide : 2 ≠ 0), sub_zero, zero_sub, neg_sq, zero_add, add_zero]
        ring

/-- The unit member of the two-vertex family has a nonzero gradient on an actual edge;
the generic theorem proves its ordered nonzero-gradient support finite. -/
theorem two_vertex_nonzero_gradient :
    (⊤ : SimpleGraph Bool).Adj false true ∧
    (if false then (1 : ℝ) else 0) ≠ (if true then (1 : ℝ) else 0) ∧
    {e : Bool × Bool | (⊤ : SimpleGraph Bool).Adj e.1 e.2 ∧
      (if e.1 then (1 : ℝ) else 0) ≠ (if e.2 then (1 : ℝ) else 0)}.Finite := by
  refine ⟨by exact (top_adj false true).mpr (by decide), by norm_num, ?_⟩
  obtain ⟨hint, henergy⟩ := two_vertex_integer_energy 1
  simpa only [Int.cast_one] using finite_nonzero_ordered_gradients hint henergy

end LatticeProb.Network

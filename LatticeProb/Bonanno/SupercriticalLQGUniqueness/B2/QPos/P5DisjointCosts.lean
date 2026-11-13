/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5DisjointCosts at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem disjoint_segment_cost_lower
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (S : α → Finset β) (U : Finset β)
    (w : β → ℝ) (R : ℝ)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (S i) (S j))
    (hsub : ∀ i ∈ F, S i ⊆ U)
    (hw : ∀ j ∈ U, 0 ≤ w j)
    (hlower : ∀ i ∈ F, R ≤ ∑ j ∈ S i, w j) :
    (F.card : ℝ) * R ≤ ∑ j ∈ U, w j := by
  have hfirst : (F.card : ℝ) * R ≤ ∑ i ∈ F, ∑ j ∈ S i, w j := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i hi => hlower i hi)
  have hunion : F.biUnion S ⊆ U := by
    intro j hj
    obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
    exact hsub i hi hj
  have hsecond : (∑ i ∈ F, ∑ j ∈ S i, w j) =
      ∑ j ∈ F.biUnion S, w j := by
    exact (Finset.sum_biUnion hdisj).symm
  rw [hsecond] at hfirst
  exact hfirst.trans (Finset.sum_le_sum_of_subset_of_nonneg hunion
    (fun j hjU _ => hw j hjU))

end SupercriticalLQGUniqueness.B2.QPos

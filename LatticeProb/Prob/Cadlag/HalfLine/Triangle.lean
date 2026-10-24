import LatticeProb.Prob.Cadlag.HalfLine.Discrepancy
import LatticeProb.Prob.Cadlag.HalfLine.TimeChange

/-!
# Symmetry and triangle inequality of the half-line distance

Inversion and composition of admissible time changes give symmetry and the triangle
inequality for the Ethier–Kurtz distance, first in extended and then in real form.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set MeasureTheory
open scoped ENNReal

variable {E : Type*} [MetricSpace E]

/-- The bounded state distance is symmetric. -/
theorem q_comm (a b : E) : q a b = q b a := by
  simp only [q, edist_comm]

/-- The bounded state distance vanishes on the diagonal. -/
theorem q_self (a : E) : q a a = 0 := by
  simp only [q, edist_self, min_eq_left zero_le_one]

/-- Truncating the state distance at one preserves the triangle inequality. -/
theorem q_triangle (a b c : E) : q a c ≤ q a b + q b c := by
  unfold q
  by_cases hab : edist a b ≤ 1
  · by_cases hbc : edist b c ≤ 1
    · simpa only [min_eq_left hab, min_eq_left hbc] using
        (min_le_left (edist a c) 1).trans (edist_triangle a b c)
    · rw [min_eq_right (le_of_not_ge hbc)]
      exact (min_le_right _ _).trans (le_add_left le_rfl)
  · rw [min_eq_right (le_of_not_ge hab)]
    exact (min_le_right _ _).trans (le_add_right le_rfl)

/-- Inverting the time change exchanges the paths in the stopped discrepancy. -/
theorem discrepancy_symm (x y : D E) (l : LambdaPrime) (u : Time) :
    discrepancy y x l.symm u = discrepancy x y l u := by
  unfold discrepancy
  apply le_antisymm
  · apply iSup_le
    intro s
    simpa only [OrderIso.apply_symm_apply, q_comm] using
      (le_iSup (fun t => q (x.1 (min t u)) (y.1 (min (l t) u))) (l.symm s))
  · apply iSup_le
    intro t
    simpa only [OrderIso.symm_apply_apply, q_comm] using
      (le_iSup (fun s => q (y.1 (min s u)) (x.1 (min (l.symm s) u))) (l t))

/-- Composing time changes bounds the stopped discrepancy by the two discrepancies. -/
theorem discrepancy_trans_le (x y z : D E) (l₁ l₂ : LambdaPrime) (u : Time) :
    discrepancy x z (l₁.trans l₂) u ≤ discrepancy x y l₁ u + discrepancy y z l₂ u := by
  unfold discrepancy
  apply iSup_le
  intro t
  exact (q_triangle _ (y.1 (min (l₁ t) u)) _).trans
    (add_le_add
      (le_iSup (fun s => q (x.1 (min s u)) (y.1 (min (l₁ s) u))) t)
      (le_iSup (fun s => q (y.1 (min s u)) (z.1 (min (l₂ s) u))) (l₁ t)))

/-- Inversion exchanges the paths in the integrated discrepancy. -/
theorem integratedDiscrepancy_symm (x y : D E) (l : LambdaPrime) :
    integratedDiscrepancy y x l.symm = integratedDiscrepancy x y l := by
  simp only [integratedDiscrepancy, discrepancy_symm]

/-- Integration preserves the composition inequality for stopped discrepancies. -/
theorem integratedDiscrepancy_trans_le (x y z : D E) (l₁ l₂ : LambdaPrime) :
    integratedDiscrepancy x z (l₁.trans l₂) ≤
      integratedDiscrepancy x y l₁ + integratedDiscrepancy y z l₂ := by
  rw [← integratedDiscrepancy_lintegral_add x y y z l₁ l₂]
  apply lintegral_mono
  intro u
  exact (mul_le_mul_right (discrepancy_trans_le x y z l₁ l₂ u.toNNReal) _).trans_eq
    (mul_add _ _ _)

/-- The extended half-line distance is symmetric. -/
theorem skorohodDistanceExtended_comm (x y : D E) :
    skorohodDistanceExtended x y = skorohodDistanceExtended y x := by
  have bound (a b : D E) : skorohodDistanceExtended a b ≤ skorohodDistanceExtended b a := by
    apply le_iInf
    intro l
    exact (iInf_le _ l.symm).trans_eq (by
      rw [Lambda.gamma_symm]
      change max (gamma l.1) (integratedDiscrepancy a b l.1.symm) = _
      rw [integratedDiscrepancy_symm])
  exact le_antisymm (bound x y) (bound y x)

/-- Composition of admissible changes proves the extended distance triangle inequality. -/
theorem skorohodDistanceExtended_triangle (x y z : D E) :
    skorohodDistanceExtended x z ≤
      skorohodDistanceExtended x y + skorohodDistanceExtended y z := by
  apply ENNReal.le_iInf_add_iInf
  intro l₁ l₂
  apply (iInf_le _ (l₁.trans l₂)).trans
  apply max_le
  · exact (Lambda.gamma_trans_le l₁ l₂).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (integratedDiscrepancy_trans_le x y z l₁.1 l₂.1).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- The identity change makes the extended distance of a path to itself zero. -/
theorem skorohodDistanceExtended_self (x : D E) : skorohodDistanceExtended x x = 0 := by
  apply le_antisymm _ bot_le
  apply (iInf_le _ identityChange).trans
  simp only [identityChange, gamma_identity, integratedDiscrepancy, discrepancy,
    OrderIso.refl_apply, q_self, iSup_const, mul_zero, lintegral_zero, max_self]
  exact le_rfl

/-- The real half-line distance is symmetric. -/
theorem skorohodDistance_comm (x y : D E) : skorohodDistance x y = skorohodDistance y x := by
  unfold skorohodDistance
  rw [skorohodDistanceExtended_comm]

/-- The real half-line distance satisfies the triangle inequality. -/
theorem skorohodDistance_triangle (x y z : D E) :
    skorohodDistance x z ≤ skorohodDistance x y + skorohodDistance y z := by
  have finite (a b : D E) : skorohodDistanceExtended a b ≠ ∞ :=
    ne_of_lt ((skorohodDistanceExtended_le_one a b).trans_lt ENNReal.one_lt_top)
  unfold skorohodDistance
  rw [← ENNReal.toReal_add (finite x y) (finite y z)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨finite x y, finite y z⟩)
    (skorohodDistanceExtended_triangle x y z)

/-- The real half-line distance vanishes on every path's diagonal. -/
theorem skorohodDistance_self (x : D E) : skorohodDistance x x = 0 := by
  simp only [skorohodDistance, skorohodDistanceExtended_self, ENNReal.toReal_zero]

/-- The real half-line distance is nonnegative. -/
theorem skorohodDistance_nonneg (x y : D E) : 0 ≤ skorohodDistance x y :=
  ENNReal.toReal_nonneg

end LatticeProb.Cadlag.HalfLine

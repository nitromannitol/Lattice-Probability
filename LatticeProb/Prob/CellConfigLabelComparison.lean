import LatticeProb.Prob.CellConfigLabelTransition

/-! # Labelled and cell transitions -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- The total conductance of an active label is the total conductance of its cell. -/
theorem rowTotal_eq_pi (H : GMSSpace) (v : Code.Vertex H.1.code) :
    rowTotal H v.val = H.1.pi (H.1.cellEquiv H.2 v) := by
  rw [CellConfig.pi_cellEquiv H.2 v]
  unfold rowTotal
  symm
  apply tsum_subtype_eq_of_support_subset
  intro n hn
  by_contra h
  have hn' : H.1.slot n = none := by
    cases hs : H.1.slot n with
    | none => rfl
    | some K =>
      apply False.elim
      apply h
      change (H.1.slot n).isSome = true
      simp [hs]
  exact hn (CellConfig.codeCond_of_none_right hn')

/-- At active labels with nonzero total conductance, the coded transition is the cell transition. -/
theorem step_eq_transition (H : GMSSpace) (v w : Code.Vertex H.1.code)
    (hpi : H.1.pi (H.1.cellEquiv H.2 v) ≠ 0) :
    step H v.val w.val = H.1.transition (H.1.cellEquiv H.2 v) (H.1.cellEquiv H.2 w) := by
  simp only [step, rowTotal_eq_pi, hpi, ↓reduceIte, CellConfig.transition]
  exact congrArg (fun x : ℝ => x / H.1.pi (H.1.cellEquiv H.2 v))
    (CellConfig.code_cond H.2 v w)

/-- An absent label is an absorbing state of the coded walk. -/
theorem step_of_absent (H : GMSSpace) (n m : ℕ) (hn : H.1.slot n = none) :
    step H n m = if m = n then 1 else 0 := by
  have hrow : rowTotal H n = 0 := by
    simp only [rowTotal, CellConfig.codeCond_of_none_left hn, tsum_zero]
  simp [step, hrow]

end LatticeProb.CellConfigLabelTransition

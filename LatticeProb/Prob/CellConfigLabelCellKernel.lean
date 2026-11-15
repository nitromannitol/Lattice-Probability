import LatticeProb.Prob.CellConfigLabelComparison
import LatticeProb.Prob.CellConfigLabelFibre
import LatticeProb.Walk.CellConfigSRWChain

/-! # Labelled and cell walk kernels -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- The labelled and cell kernels agree at occupied labels, including absorbing rows. -/
theorem fixedKernel_singleton_eq_cellKernel (H : GMSSpace) [Countable H.1.cells]
    (v w : Code.Vertex H.1.code) :
    fixedKernel H v.val {w.val} =
      CellConfigSRW.kernel H.1 (H.1.cellEquiv H.2 v) {H.1.cellEquiv H.2 w} := by
  classical
  change kernel (H, v.val) {w.val} = _
  rw [kernel_singleton]
  by_cases hp : 0 < H.1.pi (H.1.cellEquiv H.2 v)
  · rw [CellConfigSRW.kernel_singleton _ hp, step_eq_transition H v w hp.ne']
  · have hz : H.1.pi (H.1.cellEquiv H.2 v) = 0 :=
      le_antisymm (le_of_not_gt hp) (CellConfigSRW.pi_nonneg H.1 H.2 _)
    have hrow : rowTotal H v.val = 0 := (rowTotal_eq_pi H v).trans hz
    have hcell : CellConfigSRW.kernel H.1 (H.1.cellEquiv H.2 v) =
        Measure.dirac (H.1.cellEquiv H.2 v) := by
      rw [CellConfigSRW.kernel_apply, CellConfigSRW.stepMeasure, ite_eq_right hp]
    rw [hcell]
    by_cases hv : v = w
    · subst w
      simp [step, hrow, Measure.dirac_apply' _ (measurableSet_singleton _)]
    · have hl : v.val ≠ w.val := fun h => hv (Subtype.ext h)
      have hc : H.1.cellEquiv H.2 v ≠ H.1.cellEquiv H.2 w :=
        fun h => hv ((H.1.cellEquiv H.2).injective h)
      simp [step, hrow, hl.symm, hc, Measure.dirac_apply' _ (measurableSet_singleton _)]


end LatticeProb.CellConfigLabelTransition

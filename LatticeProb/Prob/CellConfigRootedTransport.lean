import LatticeProb.Prob.CellConfigRootedEnumeration

/-! # Rooted sums for an identified cell configuration -/

set_option autoImplicit false

open MeasureTheory ReflectedGMS ReflectedGMS.GMS
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

/-- An enumeration of an equal configuration indexes the rooted sum, with
conductance rows replaced by their indexed values. -/
theorem originRowSum_eq_tsum_of_config_eq {ι : Type*} (H : GMSSpace)
    (C : CellConfig) (hC : H.1 = C) (e : ι ≃ C.cells) (w : ι → ℝ)
    (hw : ∀ i, C.pi (e i) = w i) :
    originRowSum id H = ∑' i : ι,
      originAreaRatio (e i : Cell) * ENNReal.ofReal (w i) := by
  cases H with
  | mk H hH =>
    cases hC
    rw [originRowSum_eq_tsum_cells ⟨H, hH⟩ e]
    exact tsum_congr fun i => congrArg _ (congrArg ENNReal.ofReal (hw i))

end LatticeProb.CellConfigCappedSquare

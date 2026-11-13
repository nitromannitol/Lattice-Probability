/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.CellArea at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.StatementIngredients
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Positive finite cell area

Compactness of every indexed cell gives finite Lebesgue measure, while the
nonempty-interior clause of `Geometry` gives positive Lebesgue measure.  This
file only adapts the corresponding Mathlib measure lemmas to the existing
`cellArea` definition.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ReflectedGMS

theorem cellVolume_pos_lt_top {V : Type*} [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (v : V) :
    0 < volume (F.cell v : Set Plane) ∧ volume (F.cell v : Set Plane) < ∞ := by
  exact ⟨Measure.measure_pos_of_nonempty_interior volume (hF.2.1 v),
    (F.cell v).isCompact.measure_lt_top⟩

theorem StatementIngredients.cellArea_pos {V : Type*} [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (v : V) :
    0 < StatementIngredients.cellArea F v := by
  unfold StatementIngredients.cellArea
  exact ENNReal.toReal_pos (cellVolume_pos_lt_top F hF v).1.ne'
    (cellVolume_pos_lt_top F hF v).2.ne

end ReflectedGMS

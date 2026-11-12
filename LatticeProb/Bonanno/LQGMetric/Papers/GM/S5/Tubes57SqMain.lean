/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes57SqMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Main

/-!
# GM Lemma 5.7 for square tubes (task P2-M2L3, decision D66): measurability of the Borel form

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.7
(`lem-geo-event-local`, l. 2997–3018). The separation measurability (open node `SepFromMeasSq`
of D66) is no longer needed: condition (2) is read as `SepNear` (D69), an open condition on the
point, and `uMeasurableSet_tubeEventB` (`Tubes57Main.lean`) holds for every open `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- a square tube is open -/
theorem isOpen_of_isSquareTube {V : Set ℂ} {s : ℝ} {X : Set ℂ} (hV : IsSquareTube V s X) :
    IsOpen V := by
  obtain ⟨F, -, rfl⟩ := hV; exact isOpen_interior

/-- the Borel form is universally measurable (`uMeasurableSet_tubeEventB`; no separation
hypothesis is needed since condition (2) is read as `SepNear`, D69) -/
theorem uMeasurableSet_tubeEventB_of (V : Set ℂ) {D D' : DistC → ContMetric}
    (hD : Measurable D) (hD' : Measurable D') (cs Cs c₁ η b ε r : ℝ) (z : ℂ)
    (hV : IsOpen V) : UMeasurableSet (tubeEventB D D' cs Cs c₁ η b ε r z V) :=
  uMeasurableSet_tubeEventB hD hD' cs Cs c₁ η b ε r z hV

end LQGMetric.GM

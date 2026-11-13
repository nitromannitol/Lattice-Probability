/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.LocalAreaSummability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.LargeCellDiameterDecay
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Local summability of cell area

This is the deterministic content of manuscript Lemma `p:lem:localarea`.
If the maximal diameter of a cell meeting the closed ball of radius `R` is
finite, every such cell is contained in the closed ball of radius `R + D_R`.
The cell interiors are pairwise disjoint and have the same Lebesgue area as
the cells, so countable additivity bounds their total area by the area of the
enlarged ball.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS

variable {V : Type*} [Countable V]

/-- A cell meeting `B_R` lies in `B_{R + D_R}` when `D_R` is finite. -/
theorem cell_subset_closedBall_add_maxDiamHittingBall_toReal
    (F : IndexedCells V) {R : ℝ} (hR : 0 ≤ R)
    (hD : Spatial.maxDiamHittingBall F R < ∞)
    (v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v}) :
    (F.cell v.1 : Set Plane) ⊆
      Metric.closedBall (0 : Plane) (R + (Spatial.maxDiamHittingBall F R).toReal) := by
  obtain ⟨x, hxcell, hxball⟩ := v.2
  intro y hycell
  have hdiam_le : ENNReal.ofReal (Metric.diam (F.cell v.1 : Set Plane)) ≤
      Spatial.maxDiamHittingBall F R :=
    le_iSup
      (fun w : {w : V // Hits F (Metric.closedBall (0 : Plane) R) w} =>
        ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) v
  have hdiam_toReal : Metric.diam (F.cell v.1 : Set Plane) ≤
      (Spatial.maxDiamHittingBall F R).toReal := by
    rw [← ENNReal.toReal_ofReal Metric.diam_nonneg]
    exact ENNReal.toReal_mono hD.ne hdiam_le
  have hyx : dist y x ≤ Metric.diam (F.cell v.1 : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell v.1).isCompact.isBounded hycell hxcell
  have hx0 : dist x (0 : Plane) ≤ R := Metric.mem_closedBall.mp hxball
  rw [Metric.mem_closedBall]
  calc
    dist y 0 ≤ dist y x + dist x 0 := dist_triangle y x 0
    _ ≤ Metric.diam (F.cell v.1 : Set Plane) + R := add_le_add hyx hx0
    _ ≤ R + (Spatial.maxDiamHittingBall F R).toReal := by
      linarith

/-- ENNReal form of local cell-area summability.  No local finiteness of the
number of cells is assumed. -/
theorem tsum_cellVolume_hitting_closedBall_le_volume_enlargedBall
    (F : IndexedCells V) (hF : Geometry F) {R : ℝ} (hR : 0 ≤ R)
    (hD : Spatial.maxDiamHittingBall F R < ∞) :
    (∑' v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
        volume (F.cell v.1 : Set Plane)) ≤
      volume (Metric.closedBall (0 : Plane)
        (R + (Spatial.maxDiamHittingBall F R).toReal)) := by
  let I := {v : V // Hits F (Metric.closedBall (0 : Plane) R) v}
  have hpair : Pairwise
      (fun v w : I => Disjoint (interior (F.cell v.1 : Set Plane))
        (interior (F.cell w.1 : Set Plane))) := by
    intro v w hvw
    exact hF.2.2.2.1 (fun hv => hvw (Subtype.ext hv))
  have hmeasure : ∀ v : I,
      volume (interior (F.cell v.1 : Set Plane)) = volume (F.cell v.1 : Set Plane) :=
    fun v => measure_interior_of_null_frontier (hF.2.2.1 v.1)
  calc
    (∑' v : I, volume (F.cell v.1 : Set Plane)) =
        volume (⋃ v : I, interior (F.cell v.1 : Set Plane)) := by
          rw [measure_iUnion hpair (fun _ => isOpen_interior.measurableSet)]
          exact (tsum_congr hmeasure).symm
    _ ≤ volume (Metric.closedBall (0 : Plane)
          (R + (Spatial.maxDiamHittingBall F R).toReal)) := by
      apply measure_mono
      intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨v, hyv⟩
      exact cell_subset_closedBall_add_maxDiamHittingBall_toReal F hR hD v
        (interior_subset hyv)

/-- Exact numerical-area bound in manuscript Lemma `p:lem:localarea`. -/
theorem tsum_cellVolume_hitting_closedBall_le_pi_mul_sq
    (F : IndexedCells V) (hF : Geometry F) {R : ℝ} (hR : 0 ≤ R)
    (hD : Spatial.maxDiamHittingBall F R < ∞) :
    (∑' v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
        volume (F.cell v.1 : Set Plane)) ≤
      ENNReal.ofReal
        (Real.pi * (R + (Spatial.maxDiamHittingBall F R).toReal) ^ 2) := by
  have h := tsum_cellVolume_hitting_closedBall_le_volume_enlargedBall F hF hR hD
  rw [EuclideanSpace.volume_closedBall_fin_two] at h
  have hradius : 0 ≤ R + (Spatial.maxDiamHittingBall F R).toReal :=
    add_nonneg hR ENNReal.toReal_nonneg
  simpa [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hradius 2, mul_comm]
    using h

/-- The real cell areas over cells meeting a bounded ball form a summable
family and obey the manuscript's `pi * (R + D_R)^2` bound. -/
theorem summable_cellArea_hitting_closedBall_and_tsum_le
    (F : IndexedCells V) (hF : Geometry F) {R : ℝ} (hR : 0 ≤ R)
    (hD : Spatial.maxDiamHittingBall F R < ∞) :
    Summable (fun v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v} =>
      StatementIngredients.cellArea F v.1) ∧
    (∑' v : {v : V // Hits F (Metric.closedBall (0 : Plane) R) v},
        StatementIngredients.cellArea F v.1) ≤
      Real.pi * (R + (Spatial.maxDiamHittingBall F R).toReal) ^ 2 := by
  let I := {v : V // Hits F (Metric.closedBall (0 : Plane) R) v}
  let B := Real.pi * (R + (Spatial.maxDiamHittingBall F R).toReal) ^ 2
  have hB : 0 ≤ B := mul_nonneg Real.pi_pos.le (sq_nonneg _)
  have hbound : (∑' v : I, volume (F.cell v.1 : Set Plane)) ≤ ENNReal.ofReal B := by
    exact tsum_cellVolume_hitting_closedBall_le_pi_mul_sq F hF hR hD
  have hsum_ne_top : (∑' v : I, volume (F.cell v.1 : Set Plane)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hsummable : Summable (fun v : I => StatementIngredients.cellArea F v.1) := by
    simpa [StatementIngredients.cellArea] using
      (ENNReal.summable_toReal hsum_ne_top)
  refine ⟨hsummable, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.tsum_toReal_eq
      (fun v : I => (F.cell v.1).isCompact.measure_lt_top.ne),
    ENNReal.toReal_ofReal hB] at hreal
  simpa [StatementIngredients.cellArea, B] using hreal

end ReflectedGMS

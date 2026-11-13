/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SpatialRadiusEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LineVariation
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities

/-!
# Local finite energy of the spatial radius

For cell representatives `z v ∈ H_v`, adjacent-cell intersection bounds the
radius increment by the sum of the two cell diameters.  Consequently the
manuscript's deterministic local mass

`∑_{v ∈ A} diam(H_v)^2 (π(v) + π*(v))`

controls the energy of `v ↦ ‖z v‖` on the graph restricted to `A`.  The
finiteness of this mass is an explicit deterministic input here; its
probabilistic finite-expectation or mass-transport producer is separate.
-/

set_option autoImplicit false

open Set

namespace ReflectedGMS

variable {V : Type*}

theorem RootDensities.piStar_nonneg (F : IndexedCells V) (v : V) :
    0 ≤ RootDensities.piStar F v := by
  unfold RootDensities.piStar
  exact tsum_nonneg fun w => inv_nonneg.mpr (F.graph.c_nonneg v w)

/-- Representatives in two adjacent cells differ in radius by at most the sum
of the two cell diameters. -/
theorem abs_norm_sub_norm_le_cellDiameters [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : StatementIngredients.CellRepresentatives F z) {v w : V}
    (hvw : F.graph.toSimpleGraph.Adj v w) :
    |‖z w‖ - ‖z v‖| ≤
      Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane) := by
  obtain ⟨q, hqv, hqw⟩ := hF.2.2.2.2.2.2.2 hvw
  calc
    |‖z w‖ - ‖z v‖| ≤ dist (z w) (z v) := by
      simpa only [dist_eq_norm] using abs_norm_sub_norm_le (z w) (z v)
    _ ≤ dist (z w) q + dist q (z v) := dist_triangle _ _ _
    _ ≤ Metric.diam (F.cell w : Set Plane) + Metric.diam (F.cell v : Set Plane) :=
      add_le_add
        (Metric.dist_le_diam_of_mem (F.cell w).isCompact.isBounded (hz w) hqw)
        (Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hqv (hz v))
    _ = _ := add_comm _ _

/-- The exact local diameter-weighted `π + π*` mass from the manuscript is
summable on a patch whenever its `π` part is; this projection is used by the
radius-energy estimate. -/
theorem summable_localDiameterPi_of_combined [Countable V]
    (F : IndexedCells V) (A : Set V)
    (hmass : Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 *
        (RootDensities.pi F v.1 + RootDensities.piStar F v.1))) :
    Summable (fun v : A =>
      Metric.diam (F.cell v.1 : Set Plane) ^ 2 * RootDensities.pi F v.1) := by
  apply Summable.of_nonneg_of_le
      (fun v => mul_nonneg (sq_nonneg _) (F.graph.pi_nonneg v.1)) _ hmass
  intro v
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right (RootDensities.piStar_nonneg F v.1)) (sq_nonneg _)

/-- A diameter bound on cells whose representatives lie in the cutoff collar
puts both endpoints of every touching edge in the enlarged spatial patch. -/
theorem collar_subset_cells_hitting_closedBall [Countable V]
    (F : IndexedCells V) (hF : Geometry F) (z : V → Plane)
    (hz : StatementIngredients.CellRepresentatives F z) (R D : ℝ)
    (hD : ∀ v, ‖z v‖ < R + 1 → Metric.diam (F.cell v : Set Plane) ≤ D) :
    ∀ v w, F.graph.c v w ≠ 0 →
      (‖z v‖ < R + 1 ∨ ‖z w‖ < R + 1) →
      Hits F (Metric.closedBall (0 : Plane) (R + 1 + D)) v ∧
        Hits F (Metric.closedBall (0 : Plane) (R + 1 + D)) w := by
  intro v w hc hin
  have hadj : F.graph.toSimpleGraph.Adj v w :=
    lt_of_le_of_ne (F.graph.c_nonneg _ _) (Ne.symm hc)
  obtain ⟨q, hqv, hqw⟩ := hF.2.2.2.2.2.2.2 hadj
  have hqnorm : ‖q‖ < R + 1 + D := by
    rcases hin with hv | hw
    · have hd := Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hqv (hz v)
      calc
        ‖q‖ ≤ dist q (z v) + ‖z v‖ := by
          simpa only [dist_zero_right] using dist_triangle q (z v) 0
        _ < D + (R + 1) := add_lt_add_of_le_of_lt (hd.trans (hD v hv)) hv
        _ = R + 1 + D := by ring
    · have hd := Metric.dist_le_diam_of_mem (F.cell w).isCompact.isBounded hqw (hz w)
      calc
        ‖q‖ ≤ dist q (z w) + ‖z w‖ := by
          simpa only [dist_zero_right] using dist_triangle q (z w) 0
        _ < D + (R + 1) := add_lt_add_of_le_of_lt (hd.trans (hD w hw)) hw
        _ = R + 1 + D := by ring
  constructor <;> refine ⟨q, ?_, ?_⟩
  · exact hqv
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hqnorm.le
  · exact hqw
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hqnorm.le

end ReflectedGMS

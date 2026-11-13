/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.BaseSpecificEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds
import LatticeProb.Bonanno.ReflectedGMS.Limit.DirectionalNondegeneracy

/-!
# The base embedding has finite specific energy (`s:lem:e0`)

This module proves the manuscript lemma *The base embedding has finite specific energy*
with its original normalisation: with

`M_π = E[d_{H_0}² π(H_0) / a_{H_0}]`,   `e_0 = ‖∇b‖_*² = E[ρ_{∇b}(ω, 0)]`,

one has `e_0 ≤ 2 M_π < ∞`, where `ρ` is the manuscript specific-energy density

`ρ_θ(ω, z) = (2 a_{H_z})⁻¹ ∑_{H' ∼ H_z} c(H_z, H') |θ(H_z, H')|²`

evaluated on the *centroid* (base) embedding `b_H = a_H⁻¹ ∫_H z dz`.  The rooted density is
the existing boundary-masked `RootDensities.rootedSpecificEnergyDensity` of
`StatementIngredients.cellCentroid`, so the factor `1/2` in the endpoint energy and the final
constant `2` are both the manuscript ones.

The proof is the manuscript proof, with no expectation identity left as a hypothesis.

* **Deterministic step.** By the centroid estimate `|b_H - b_{H'}| ≤ d_H + d_{H'}` for adjacent
  cells (`s:eq:centroid`, reused from `DirectionalNondegeneracy.dist_cellCentroid_le_diam`),
  `ρ_{∇b}(H) ≤ d_H² π(H)/a_H + a_H⁻¹ ∑_{H' ∼ H} c(H,H') d_{H'}²`,
  i.e. the rooted centroid energy is at most its own weighted diameter density plus the
  neighbour weighted diameter density (`specificEnergyDensity_cellCentroid_le`).

* **Mass transport.** The two terms have the same expectation.  This is carried out with the
  *actual* manuscript edge transport
  `T(𝓗, w, z) = c(H_w, H_z) d_{H_z}² / (a_{H_w} a_{H_z}) 1_{H_w ∼ H_z}`,
  realised as an honest `EnvironmentLaws.MassTransportKernel`: conductances are similarity
  invariant, `d²` scales by `s²` and each of the two areas by `s²`, so the transport is exactly
  `(s²)⁻¹`-covariant.  Its outgoing integral from the origin is the neighbour weighted diameter
  density and its incoming integral at the origin is `d_{H_0}² π(H_0)/a_{H_0}`, both off the
  boundary mask (`Spatial.ae_notMem_boundaryMask_of_massTransport`).

* **(FE) application.** `d_H² π(H)/a_H ≤ (d_H²/a_H)(π(H) + π*(H))` pointwise, so the finite
  energy moment `E[rootedFiniteEnergyDensity] ≠ ∞` of the manuscript hypothesis (FE) gives
  `M_π < ∞`.

Nothing here assumes ergodicity, a canonical relabelling action, finiteness of the cell count, or
finite local patch energy; the local patch statement is a separate deterministic module.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ReflectedGMS.BaseSpecificEnergy

open Code EnvironmentLaws Spatial

variable {V : Type*}

/-! ### Elementary `ℝ≥0∞` rearrangements -/

/-- Cancelling the manuscript factor `2` from the endpoint energy and its `2 a_H` denominator. -/
theorem two_mul_div_two_mul (x a : ℝ≥0∞) : 2 * x / (2 * a) = x / a := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := by simp
  have h2' : (2 : ℝ≥0∞) ≠ ∞ := by simp
  have hinv : ((2 : ℝ≥0∞) * a)⁻¹ = (2 : ℝ≥0∞)⁻¹ * a⁻¹ :=
    ENNReal.mul_inv (Or.inl h2) (Or.inl h2')
  rw [div_eq_mul_inv, div_eq_mul_inv, hinv, mul_mul_mul_comm,
    ENNReal.mul_inv_cancel h2 h2', one_mul]

/-- The scaling rearrangement behind degree `-2` covariance of the edge transport: one factor
`s²` from `d²` against two factors `s²` from the two areas. -/
theorem transportRescale (x c D VK VL t ti : ℝ≥0∞) (ht : t * ti = 1) :
    x * c * (t * D) * (ti * VK) * (ti * VL) = ti * (x * c * D * VK * VL) := by
  calc x * c * (t * D) * (ti * VK) * (ti * VL)
      = t * ti * (ti * (x * c * D * VK * VL)) := by ring
    _ = ti * (x * c * D * VK * VL) := by rw [ht, one_mul]

/-- `ENNReal.ofReal` of a doubled nonnegative real. -/
theorem ofReal_two_mul (x : ℝ) :
    ENNReal.ofReal (2 * x) = 2 * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  simp

/-! ### The two rooted diameter densities of the manuscript proof -/

/-- The manuscript integrand of `M_π`: `d_H² π(H) / a_H`. -/
noncomputable def diamSqPiDensity (F : IndexedCells V) (v : V) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
      ENNReal.ofReal (RootDensities.pi F v) /
    ENNReal.ofReal (StatementIngredients.cellArea F v)

/-- The neighbour weighted diameter density `a_H⁻¹ ∑_{H' ∼ H} c(H,H') d_{H'}²`. -/
noncomputable def neighborDiamSqDensity (F : IndexedCells V) (v : V) : ℝ≥0∞ :=
  (∑' w : V, ENNReal.ofReal (F.graph.c v w) *
      ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) /
    ENNReal.ofReal (StatementIngredients.cellArea F v)

/-- Boundary-masked `d_{H_0}² π(H_0) / a_{H_0}`. -/
noncomputable def rootedDiamSqPiDensity (F : IndexedCells V) (z : Plane) : ℝ≥0∞ :=
  (RootDensities.rootAt F z).elim 0 (diamSqPiDensity F)

/-- Boundary-masked `a_{H_0}⁻¹ ∑_{H' ∼ H_0} c(H_0,H') d_{H'}²`. -/
noncomputable def rootedNeighborDiamSqDensity (F : IndexedCells V) (z : Plane) : ℝ≥0∞ :=
  (RootDensities.rootAt F z).elim 0 (neighborDiamSqDensity F)

/-- The manuscript `π(H)` is the total conductance sum at `H`. -/
theorem pi_eq_tsum (F : IndexedCells V) (v : V) :
    RootDensities.pi F v = ∑' w : V, F.graph.c v w := rfl

theorem ofReal_pi_eq_tsum (F : IndexedCells V) (v : V) :
    ENNReal.ofReal (RootDensities.pi F v) = ∑' w : V, ENNReal.ofReal (F.graph.c v w) := by
  rw [pi_eq_tsum]
  exact ENNReal.ofReal_tsum_of_nonneg (fun w => F.graph.c_nonneg v w) (F.graph.summable_c v)

/-! ### `M_π` is finite under the manuscript finite-energy moment (FE) -/

/-- `d_H² π(H)/a_H ≤ (d_H²/a_H)(π(H) + π*(H))`: the `M_π` integrand is dominated by the (FE)
integrand, because `π*` is nonnegative. -/
theorem diamSqPiDensity_le_finiteEnergyDensity (F : IndexedCells V) (v : V) :
    diamSqPiDensity F v ≤ RootDensities.finiteEnergyDensity F v := by
  rw [diamSqPiDensity, RootDensities.finiteEnergyDensity, div_eq_mul_inv, div_eq_mul_inv]
  calc ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
        ENNReal.ofReal (RootDensities.pi F v) *
        (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹
      = ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
          (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ *
          ENNReal.ofReal (RootDensities.pi F v) := by ring
    _ ≤ ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
          (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ *
          (ENNReal.ofReal (RootDensities.pi F v) +
            ENNReal.ofReal (RootDensities.piStar F v)) :=
        mul_le_mul' le_rfl le_self_add

theorem rootedDiamSqPiDensity_le_rootedFiniteEnergyDensity (F : IndexedCells V) (z : Plane) :
    rootedDiamSqPiDensity F z ≤ RootDensities.rootedFiniteEnergyDensity F z := by
  cases hroot : RootDensities.rootAt F z with
  | none => simp [rootedDiamSqPiDensity, RootDensities.rootedFiniteEnergyDensity, hroot]
  | some v =>
      simp only [rootedDiamSqPiDensity, RootDensities.rootedFiniteEnergyDensity, hroot,
        Option.elim]
      exact diamSqPiDensity_le_finiteEnergyDensity F v

/-! ### The deterministic centroid bound (`s:eq:centroid`) -/

/-- **The manuscript centroid estimate.** Adjacent cells intersect, so their centroids differ by
at most the sum of the two cell diameters.  This is the two-point form of
`DirectionalNondegeneracy.dist_cellCentroid_le_diam`. -/
theorem dist_cellCentroid_le_add_diam_of_adj [Countable V] (F : IndexedCells V)
    (hF : Geometry F) {v w : V} (hvw : F.graph.toSimpleGraph.Adj v w) :
    dist (StatementIngredients.cellCentroid F v) (StatementIngredients.cellCentroid F w) ≤
      Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane) := by
  obtain ⟨q, hqv, hqw⟩ := hF.2.2.2.2.2.2.2 hvw
  calc dist (StatementIngredients.cellCentroid F v) (StatementIngredients.cellCentroid F w)
      ≤ dist (StatementIngredients.cellCentroid F v) q +
          dist q (StatementIngredients.cellCentroid F w) := dist_triangle _ _ _
    _ ≤ Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane) := by
        refine add_le_add (DirectionalNondegeneracy.dist_cellCentroid_le_diam F hF v hqv) ?_
        rw [dist_comm]
        exact DirectionalNondegeneracy.dist_cellCentroid_le_diam F hF w hqw

/-- **First milestone.** The deterministic rooted centroid energy density at a vertex is at most
its own weighted diameter density plus the neighbour weighted diameter density.  The factor `1/2`
of the endpoint energy is exactly what turns `|b_H - b_{H'}|² ≤ 2 d_H² + 2 d_{H'}²` into this
bound with constant `1` on each term. -/
theorem specificEnergyDensity_cellCentroid_le [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (v : V) :
    RootDensities.specificEnergyDensity F (StatementIngredients.cellCentroid F) v
      ≤ diamSqPiDensity F v + neighborDiamSqDensity F v := by
  have hterm : ∀ w : V,
      ENNReal.ofReal (F.graph.c v w) *
          ENNReal.ofReal (‖StatementIngredients.cellCentroid F w -
            StatementIngredients.cellCentroid F v‖ ^ 2)
        ≤ ENNReal.ofReal (F.graph.c v w) *
            (2 * ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) +
              2 * ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) := by
    intro w
    rcases eq_or_lt_of_le (F.graph.c_nonneg v w) with h | h
    · simp [← h]
    · have hadj : F.graph.toSimpleGraph.Adj v w := h
      have hle : ‖StatementIngredients.cellCentroid F w -
            StatementIngredients.cellCentroid F v‖
          ≤ Metric.diam (F.cell v : Set Plane) + Metric.diam (F.cell w : Set Plane) := by
        rw [norm_sub_rev, ← dist_eq_norm]
        exact dist_cellCentroid_le_add_diam_of_adj F hF hadj
      have h0 : (0 : ℝ) ≤ ‖StatementIngredients.cellCentroid F w -
          StatementIngredients.cellCentroid F v‖ := norm_nonneg _
      have hsq : ‖StatementIngredients.cellCentroid F w -
            StatementIngredients.cellCentroid F v‖ ^ 2
          ≤ 2 * Metric.diam (F.cell v : Set Plane) ^ 2 +
            2 * Metric.diam (F.cell w : Set Plane) ^ 2 := by
        nlinarith [sq_nonneg (Metric.diam (F.cell v : Set Plane) -
          Metric.diam (F.cell w : Set Plane)),
          (Metric.diam_nonneg : (0 : ℝ) ≤ Metric.diam (F.cell v : Set Plane)),
          (Metric.diam_nonneg : (0 : ℝ) ≤ Metric.diam (F.cell w : Set Plane))]
      refine mul_le_mul' le_rfl ?_
      calc ENNReal.ofReal (‖StatementIngredients.cellCentroid F w -
              StatementIngredients.cellCentroid F v‖ ^ 2)
          ≤ ENNReal.ofReal (2 * Metric.diam (F.cell v : Set Plane) ^ 2 +
              2 * Metric.diam (F.cell w : Set Plane) ^ 2) := ENNReal.ofReal_le_ofReal hsq
        _ = 2 * ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) +
              2 * ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ofReal_two_mul, ofReal_two_mul]
  have hstep : ∀ w : V,
      ENNReal.ofReal (F.graph.c v w) *
          (2 * ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) +
            2 * ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2))
        = 2 * (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              ENNReal.ofReal (F.graph.c v w)) +
          2 * (ENNReal.ofReal (F.graph.c v w) *
              ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) := by
    intro w
    ring
  have hsum : (∑' w : V, ENNReal.ofReal (F.graph.c v w) *
        ENNReal.ofReal (‖StatementIngredients.cellCentroid F w -
          StatementIngredients.cellCentroid F v‖ ^ 2))
      ≤ 2 * (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
            ENNReal.ofReal (RootDensities.pi F v) +
          ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
            ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) := by
    calc (∑' w : V, ENNReal.ofReal (F.graph.c v w) *
          ENNReal.ofReal (‖StatementIngredients.cellCentroid F w -
            StatementIngredients.cellCentroid F v‖ ^ 2))
        ≤ ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
            (2 * ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) +
              2 * ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) :=
          ENNReal.tsum_le_tsum hterm
      _ = ∑' w : V, (2 * (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              ENNReal.ofReal (F.graph.c v w)) +
            2 * (ENNReal.ofReal (F.graph.c v w) *
              ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2))) := tsum_congr hstep
      _ = (∑' w : V, 2 * (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              ENNReal.ofReal (F.graph.c v w))) +
            ∑' w : V, 2 * (ENNReal.ofReal (F.graph.c v w) *
              ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) := ENNReal.tsum_add
      _ = 2 * (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              ENNReal.ofReal (RootDensities.pi F v)) +
            2 * ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
              ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
            ofReal_pi_eq_tsum]
      _ = 2 * (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              ENNReal.ofReal (RootDensities.pi F v) +
            ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
              ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) := (mul_add _ _ _).symm
  calc RootDensities.specificEnergyDensity F (StatementIngredients.cellCentroid F) v
      = (∑' w : V, ENNReal.ofReal (F.graph.c v w) *
            ENNReal.ofReal (‖StatementIngredients.cellCentroid F w -
              StatementIngredients.cellCentroid F v‖ ^ 2)) /
          (2 * ENNReal.ofReal (StatementIngredients.cellArea F v)) := rfl
    _ ≤ (2 * (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              ENNReal.ofReal (RootDensities.pi F v) +
            ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
              ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2))) /
          (2 * ENNReal.ofReal (StatementIngredients.cellArea F v)) :=
        ENNReal.div_le_div_right hsum _
    _ = (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              ENNReal.ofReal (RootDensities.pi F v) +
            ∑' w : V, ENNReal.ofReal (F.graph.c v w) *
              ENNReal.ofReal (Metric.diam (F.cell w : Set Plane) ^ 2)) /
          ENNReal.ofReal (StatementIngredients.cellArea F v) := two_mul_div_two_mul _ _
    _ = diamSqPiDensity F v + neighborDiamSqDensity F v := by
        rw [diamSqPiDensity, neighborDiamSqDensity, div_eq_mul_inv, div_eq_mul_inv,
          div_eq_mul_inv, add_mul]

/-- The boundary-masked form of the first milestone. -/
theorem rootedSpecificEnergyDensity_cellCentroid_le [Countable V] (F : IndexedCells V)
    (hF : Geometry F) (z : Plane) :
    RootDensities.rootedSpecificEnergyDensity F (StatementIngredients.cellCentroid F) z
      ≤ rootedDiamSqPiDensity F z + rootedNeighborDiamSqDensity F z := by
  cases hroot : RootDensities.rootAt F z with
  | none =>
      simp [RootDensities.rootedSpecificEnergyDensity, rootedDiamSqPiDensity,
        rootedNeighborDiamSqDensity, hroot]
  | some v =>
      simp only [RootDensities.rootedSpecificEnergyDensity, rootedDiamSqPiDensity,
        rootedNeighborDiamSqDensity, hroot, Option.elim]
      exact specificEnergyDensity_cellCentroid_le F hF v

/-! ### The manuscript edge transport `T(𝓗,w,z) = c(H_w,H_z) d_{H_z}²/(a_{H_w} a_{H_z})` -/

/-- The indicator of the interior of a cell, as a jointly measurable `ℝ≥0∞`-valued function. -/
noncomputable def interiorIndicator (K : CompactCell) (w : Plane) : ℝ≥0∞ :=
  Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)) w

theorem measurable_interiorIndicator :
    Measurable fun p : CompactCell × Plane => interiorIndicator p.1 p.2 := by
  have hEq : (fun p : CompactCell × Plane => interiorIndicator p.1 p.2)
      = Set.indicator {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)}
          (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    show Set.indicator (interior (p.1 : Set Plane)) (fun _ => (1 : ℝ≥0∞)) p.2
      = Set.indicator {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)}
          (fun _ => (1 : ℝ≥0∞)) p
    by_cases hp : p.2 ∈ interior (p.1 : Set Plane)
    · rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem
          (show p ∈ {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)} from hp)]
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem
          (show p ∉ {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)} from hp)]
  rw [hEq]
  exact measurable_const.indicator measurableSet_cellInterior

theorem interiorIndicator_of_mem {K : CompactCell} {w : Plane}
    (hw : w ∈ interior (K : Set Plane)) : interiorIndicator K w = 1 :=
  Set.indicator_of_mem hw _

theorem interiorIndicator_of_notMem {K : CompactCell} {w : Plane}
    (hw : w ∉ interior (K : Set Plane)) : interiorIndicator K w = 0 :=
  Set.indicator_of_notMem hw _

/-- The contribution of one ordered pair of cells to the manuscript edge transport
`T(𝓗, w, z) = c(H_w, H_z) d_{H_z}² / (a_{H_w} a_{H_z}) 1_{H_w ∼ H_z}`.  Non-adjacent pairs have
`c = 0` and therefore transport nothing, exactly as the manuscript indicator does. -/
noncomputable def cellPairEnergyTransport (K L : CompactCell) (a : ℝ) (w z : Plane) : ℝ≥0∞ :=
  interiorIndicator K w * interiorIndicator L z * ENNReal.ofReal a *
      ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) *
    (volume (K : Set Plane))⁻¹ * (volume (L : Set Plane))⁻¹

theorem measurable_cellPairEnergyTransport_target (K L : CompactCell) (a : ℝ) (w : Plane) :
    Measurable fun z : Plane => cellPairEnergyTransport K L a w z := by
  have hEq : (fun z : Plane => cellPairEnergyTransport K L a w z)
      = fun z : Plane =>
        (interiorIndicator K w * ENNReal.ofReal a *
            ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) *
            (volume (K : Set Plane))⁻¹ * (volume (L : Set Plane))⁻¹) *
          interiorIndicator L z := by
    funext z
    simp only [cellPairEnergyTransport]
    ring
  rw [hEq]
  refine measurable_const.mul ?_
  show Measurable (Set.indicator (interior (L : Set Plane)) (fun _ => (1 : ℝ≥0∞)))
  exact measurable_const.indicator isOpen_interior.measurableSet

theorem measurable_cellPairEnergyTransport_source (K L : CompactCell) (a : ℝ) (z : Plane) :
    Measurable fun w : Plane => cellPairEnergyTransport K L a w z := by
  have hEq : (fun w : Plane => cellPairEnergyTransport K L a w z)
      = fun w : Plane =>
        (interiorIndicator L z * ENNReal.ofReal a *
            ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) *
            (volume (K : Set Plane))⁻¹ * (volume (L : Set Plane))⁻¹) *
          interiorIndicator K w := by
    funext w
    simp only [cellPairEnergyTransport]
    ring
  rw [hEq]
  refine measurable_const.mul ?_
  show Measurable (Set.indicator (interior (K : Set Plane)) (fun _ => (1 : ℝ≥0∞)))
  exact measurable_const.indicator isOpen_interior.measurableSet

/-- **Degree `-2` covariance of the edge transport.**  Conductances are similarity invariant,
`d_{H_z}²` scales by `s²` and each of the two areas scales by `s²`. -/
theorem cellPairEnergyTransport_transformCell (s : ℝ) (u : Plane) (hs : 0 < s)
    (K L : CompactCell) (a : ℝ) (w z : Plane) :
    cellPairEnergyTransport (transformCell s u hs K) (transformCell s u hs L) a
        (positiveSimilarity s u w) (positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * cellPairEnergyTransport K L a w z := by
  have hspos : (0 : ℝ) < s ^ 2 := by positivity
  have ht0 : ENNReal.ofReal (s ^ 2) ≠ 0 := by simpa using hspos.ne'
  have httop : ENNReal.ofReal (s ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
  have hcancel : ENNReal.ofReal (s ^ 2) * (ENNReal.ofReal (s ^ 2))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel ht0 httop
  have hindK : interiorIndicator (transformCell s u hs K) (positiveSimilarity s u w)
      = interiorIndicator K w :=
    indicator_one_congr_of_iff (mem_interior_transformCell_iff s u hs K w)
  have hindL : interiorIndicator (transformCell s u hs L) (positiveSimilarity s u z)
      = interiorIndicator L z :=
    indicator_one_congr_of_iff (mem_interior_transformCell_iff s u hs L z)
  have hdiam : ENNReal.ofReal
        (Metric.diam ((transformCell s u hs L : CompactCell) : Set Plane) ^ 2)
      = ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) := by
    rw [coe_transformCell, diam_image_positiveSimilarity s u hs, mul_pow,
      ENNReal.ofReal_mul (le_of_lt hspos)]
  have hvolK : (volume ((transformCell s u hs K : CompactCell) : Set Plane))⁻¹
      = (ENNReal.ofReal (s ^ 2))⁻¹ * (volume (K : Set Plane))⁻¹ := by
    rw [coe_transformCell, volume_image_positiveSimilarity s u (K : Set Plane),
      ENNReal.mul_inv (Or.inl ht0) (Or.inl httop)]
  have hvolL : (volume ((transformCell s u hs L : CompactCell) : Set Plane))⁻¹
      = (ENNReal.ofReal (s ^ 2))⁻¹ * (volume (L : Set Plane))⁻¹ := by
    rw [coe_transformCell, volume_image_positiveSimilarity s u (L : Set Plane),
      ENNReal.mul_inv (Or.inl ht0) (Or.inl httop)]
  rw [cellPairEnergyTransport, cellPairEnergyTransport, hindK, hindL, hdiam, hvolK, hvolL,
    transportRescale (interiorIndicator K w * interiorIndicator L z) (ENNReal.ofReal a)
      (ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2)) (volume (K : Set Plane))⁻¹
      (volume (L : Set Plane))⁻¹ (ENNReal.ofReal (s ^ 2)) (ENNReal.ofReal (s ^ 2))⁻¹ hcancel,
    ENNReal.ofReal_inv_of_pos hspos]

/-! ### Slot and environment level transport -/

/-- A pair carrying no conductance transports nothing: this is the manuscript indicator
`1_{H_w ∼ H_z}`, since non-adjacent cells have `c = 0`. -/
theorem cellPairEnergyTransport_of_zero (K L : CompactCell) (w z : Plane) :
    cellPairEnergyTransport K L 0 w z = 0 := by
  rw [cellPairEnergyTransport, ENNReal.ofReal_zero]
  ring

/-- The edge transport of an ordered pair of code slots.  An absent slot is read through the
measurable default `referenceCell`; absent slots carry no conductance
(`Code.AdmissibleConductance.absent`) and therefore transport nothing, by
`slotPairEnergyTransport_of_zero`. -/
noncomputable def slotPairEnergyTransport (o p : Option CompactCell) (a : ℝ) (w z : Plane) :
    ℝ≥0∞ :=
  cellPairEnergyTransport (o.getD referenceCell) (p.getD referenceCell) a w z

theorem slotPairEnergyTransport_of_zero (o p : Option CompactCell) (w z : Plane) :
    slotPairEnergyTransport o p 0 w z = 0 := by
  rw [slotPairEnergyTransport]
  exact cellPairEnergyTransport_of_zero _ _ w z

/-- The manuscript edge transport on the full trace environment space. -/
noncomputable def energyTransport (p : Env × Plane × Plane) : ℝ≥0∞ :=
  ∑' q : ℕ × ℕ, slotPairEnergyTransport (p.1.val.1 q.1) (p.1.val.1 q.2)
    (p.1.val.2 q.1 q.2) p.2.1 p.2.2

theorem measurable_energyTransport : Measurable energyTransport := by
  have hslot : ∀ q : ℕ × ℕ, Measurable fun p : Env × Plane × Plane =>
      slotPairEnergyTransport (p.1.val.1 q.1) (p.1.val.1 q.2) (p.1.val.2 q.1 q.2) p.2.1 p.2.2 := by
    intro q
    have hcode : Measurable fun p : Env × Plane × Plane => p.1.val :=
      measurable_inclusion.comp measurable_fst
    have h1 : Measurable fun p : Env × Plane × Plane =>
        ((p.1.val.1 q.1).getD referenceCell : CompactCell) :=
      measurable_slotCell.comp ((measurable_pi_apply q.1).comp (measurable_fst.comp hcode))
    have h2 : Measurable fun p : Env × Plane × Plane =>
        ((p.1.val.1 q.2).getD referenceCell : CompactCell) :=
      measurable_slotCell.comp ((measurable_pi_apply q.2).comp (measurable_fst.comp hcode))
    have h3 : Measurable fun p : Env × Plane × Plane => p.1.val.2 q.1 q.2 :=
      (measurable_pi_apply q.2).comp
        ((measurable_pi_apply q.1).comp (measurable_snd.comp hcode))
    have hw : Measurable fun p : Env × Plane × Plane => p.2.1 :=
      measurable_fst.comp measurable_snd
    have hz : Measurable fun p : Env × Plane × Plane => p.2.2 :=
      measurable_snd.comp measurable_snd
    have m1 : Measurable fun p : Env × Plane × Plane =>
        interiorIndicator ((p.1.val.1 q.1).getD referenceCell) p.2.1 :=
      measurable_interiorIndicator.comp (h1.prodMk hw)
    have m2 : Measurable fun p : Env × Plane × Plane =>
        interiorIndicator ((p.1.val.1 q.2).getD referenceCell) p.2.2 :=
      measurable_interiorIndicator.comp (h2.prodMk hz)
    have m3 : Measurable fun p : Env × Plane × Plane =>
        ENNReal.ofReal (p.1.val.2 q.1 q.2) := ENNReal.measurable_ofReal.comp h3
    have m4 : Measurable fun p : Env × Plane × Plane =>
        ENNReal.ofReal (Metric.diam
          (((p.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_cellDiam.comp h2).pow_const 2)
    have m5 : Measurable fun p : Env × Plane × Plane =>
        (volume (((p.1.val.1 q.1).getD referenceCell : CompactCell) : Set Plane))⁻¹ :=
      (measurable_cellVolume.comp h1).inv
    have m6 : Measurable fun p : Env × Plane × Plane =>
        (volume (((p.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane))⁻¹ :=
      (measurable_cellVolume.comp h2).inv
    have hEq : (fun p : Env × Plane × Plane =>
          slotPairEnergyTransport (p.1.val.1 q.1) (p.1.val.1 q.2) (p.1.val.2 q.1 q.2)
            p.2.1 p.2.2)
        = fun p : Env × Plane × Plane =>
          interiorIndicator ((p.1.val.1 q.1).getD referenceCell) p.2.1 *
              interiorIndicator ((p.1.val.1 q.2).getD referenceCell) p.2.2 *
              ENNReal.ofReal (p.1.val.2 q.1 q.2) *
              ENNReal.ofReal (Metric.diam
                (((p.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane) ^ 2) *
            (volume (((p.1.val.1 q.1).getD referenceCell : CompactCell) : Set Plane))⁻¹ *
            (volume (((p.1.val.1 q.2).getD referenceCell : CompactCell) : Set Plane))⁻¹ := by
      funext p
      rw [slotPairEnergyTransport, cellPairEnergyTransport]
    rw [hEq]
    exact ((((m1.mul m2).mul m3).mul m4).mul m5).mul m6
  exact Measurable.ennreal_tsum hslot

theorem energyTransport_eq_tsum_vertex (e : Env) (w z : Plane) :
    energyTransport (e, w, z)
      = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z := by
  have hadm : AdmissibleConductance e.val := e.property.choose
  have hinner : ∀ n : ℕ,
      (∑' m : ℕ, slotPairEnergyTransport (e.val.1 n) (e.val.1 m) (e.val.2 n m) w z)
        = ∑' v' : Vertex e.val, slotPairEnergyTransport (e.val.1 n)
            (some ((decode e).cell v')) (e.val.2 n v'.val) w z := by
    intro n
    have hsupp : Function.support
        (fun m : ℕ => slotPairEnergyTransport (e.val.1 n) (e.val.1 m) (e.val.2 n m) w z)
        ⊆ {m : ℕ | (e.val.1 m).isSome} := by
      intro m hm
      cases hcase : e.val.1 m with
      | none =>
          refine absurd (show slotPairEnergyTransport (e.val.1 n) (e.val.1 m)
            (e.val.2 n m) w z = 0 from ?_) hm
          rw [hadm.absent n m (Or.inr hcase)]
          exact slotPairEnergyTransport_of_zero _ _ w z
      | some L => simp [hcase]
    have hterm : ∀ v' : Vertex e.val,
        slotPairEnergyTransport (e.val.1 n) (e.val.1 v'.val) (e.val.2 n v'.val) w z
          = slotPairEnergyTransport (e.val.1 n) (some ((decode e).cell v'))
            (e.val.2 n v'.val) w z := by
      intro v'
      have hv' : e.val.1 v'.val = some ((decode e).cell v') := (Option.some_get v'.property).symm
      rw [hv']
    calc (∑' m : ℕ, slotPairEnergyTransport (e.val.1 n) (e.val.1 m) (e.val.2 n m) w z)
        = ∑' m : {m : ℕ | (e.val.1 m).isSome},
            slotPairEnergyTransport (e.val.1 n) (e.val.1 m.val) (e.val.2 n m.val) w z :=
          (tsum_subtype_eq_of_support_subset hsupp).symm
      _ = ∑' v' : Vertex e.val, slotPairEnergyTransport (e.val.1 n)
            (some ((decode e).cell v')) (e.val.2 n v'.val) w z := tsum_congr hterm
  have houter : Function.support
      (fun n : ℕ => ∑' v' : Vertex e.val, slotPairEnergyTransport (e.val.1 n)
        (some ((decode e).cell v')) (e.val.2 n v'.val) w z)
      ⊆ {n : ℕ | (e.val.1 n).isSome} := by
    intro n hn
    cases hcase : e.val.1 n with
    | none =>
        refine absurd (show (∑' v' : Vertex e.val,
          slotPairEnergyTransport (e.val.1 n) (some ((decode e).cell v'))
            (e.val.2 n v'.val) w z) = 0 from ?_) hn
        refine ENNReal.tsum_eq_zero.mpr fun v' => ?_
        rw [hadm.absent n v'.val (Or.inl hcase)]
        exact slotPairEnergyTransport_of_zero _ _ w z
    | some K => simp [hcase]
  have houterterm : ∀ v : Vertex e.val,
      (∑' v' : Vertex e.val, slotPairEnergyTransport (e.val.1 v.val)
          (some ((decode e).cell v')) (e.val.2 v.val v'.val) w z)
        = ∑' v' : Vertex e.val, cellPairEnergyTransport ((decode e).cell v)
            ((decode e).cell v') ((decode e).graph.c v v') w z := by
    intro v
    have hv : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
    refine tsum_congr fun v' => ?_
    calc slotPairEnergyTransport (e.val.1 v.val) (some ((decode e).cell v'))
            (e.val.2 v.val v'.val) w z
        = slotPairEnergyTransport (some ((decode e).cell v)) (some ((decode e).cell v'))
            (e.val.2 v.val v'.val) w z := by rw [hv]
      _ = cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z := rfl
  calc energyTransport (e, w, z)
      = ∑' q : ℕ × ℕ, slotPairEnergyTransport (e.val.1 q.1) (e.val.1 q.2)
          (e.val.2 q.1 q.2) w z := rfl
    _ = ∑' n : ℕ, ∑' m : ℕ, slotPairEnergyTransport (e.val.1 n) (e.val.1 m)
          (e.val.2 n m) w z := ENNReal.tsum_prod'
    _ = ∑' n : ℕ, ∑' v' : Vertex e.val, slotPairEnergyTransport (e.val.1 n)
          (some ((decode e).cell v')) (e.val.2 n v'.val) w z := tsum_congr hinner
    _ = ∑' n : {n : ℕ | (e.val.1 n).isSome}, ∑' v' : Vertex e.val,
          slotPairEnergyTransport (e.val.1 n.val) (some ((decode e).cell v'))
            (e.val.2 n.val v'.val) w z := (tsum_subtype_eq_of_support_subset houter).symm
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z := tsum_congr houterterm

theorem energyTransport_covariant (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : Env)
    (hsim : IsSimilarity s u hs e e') (w z : Plane) :
    energyTransport (e', positiveSimilarity s u w, positiveSimilarity s u z)
      = ENNReal.ofReal ((s ^ 2)⁻¹) * energyTransport (e, w, z) := by
  obtain ⟨relabel, hcell, hc⟩ := hsim
  rw [energyTransport_eq_tsum_vertex, energyTransport_eq_tsum_vertex,
    ← Equiv.tsum_eq relabel (fun a : Vertex e'.val => ∑' b : Vertex e'.val,
      cellPairEnergyTransport ((decode e').cell a) ((decode e').cell b)
        ((decode e').graph.c a b) (positiveSimilarity s u w) (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  rw [← Equiv.tsum_eq relabel (fun b : Vertex e'.val =>
      cellPairEnergyTransport ((decode e').cell (relabel v)) ((decode e').cell b)
        ((decode e').graph.c (relabel v) b) (positiveSimilarity s u w)
        (positiveSimilarity s u z)),
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v' => ?_
  rw [hc v v', hcell v, hcell v', cellPairEnergyTransport_transformCell]

/-- The manuscript edge transport as an actual `MassTransportKernel`. -/
noncomputable def energyTransportKernel : MassTransportKernel where
  toFun := energyTransport
  measurable_toFun := measurable_energyTransport
  covariant := fun s u hs e e' hsim w z => energyTransport_covariant s u hs e e' hsim w z

/-! ### Outgoing and incoming integrals -/

theorem lintegral_cellPairEnergyTransport_target (K L : CompactCell) (a : ℝ) (w : Plane)
    (hfrontL : volume (frontier (L : Set Plane)) = 0)
    (hposL : 0 < volume (L : Set Plane)) (hfinL : volume (L : Set Plane) < ∞) :
    (∫⁻ z : Plane, cellPairEnergyTransport K L a w z ∂volume)
      = interiorIndicator K w * ENNReal.ofReal a *
          ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) * (volume (K : Set Plane))⁻¹ := by
  have hI : MeasurableSet (interior (L : Set Plane)) := isOpen_interior.measurableSet
  have hz : ∀ z : Plane, cellPairEnergyTransport K L a w z
      = Set.indicator (interior (L : Set Plane))
        (fun _ => interiorIndicator K w * ENNReal.ofReal a *
          ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) * (volume (K : Set Plane))⁻¹ *
          (volume (L : Set Plane))⁻¹) z := by
    intro z
    by_cases hzI : z ∈ interior (L : Set Plane)
    · rw [Set.indicator_of_mem hzI, cellPairEnergyTransport, interiorIndicator_of_mem hzI]
      ring
    · rw [Set.indicator_of_notMem hzI, cellPairEnergyTransport,
        interiorIndicator_of_notMem hzI]
      ring
  simp_rw [hz]
  rw [lintegral_indicator_const hI, volume_interior_eq_of_frontier_null hfrontL, mul_assoc,
    ENNReal.inv_mul_cancel hposL.ne' hfinL.ne, mul_one]

theorem lintegral_cellPairEnergyTransport_source (K L : CompactCell) (a : ℝ) (z : Plane)
    (hfrontK : volume (frontier (K : Set Plane)) = 0)
    (hposK : 0 < volume (K : Set Plane)) (hfinK : volume (K : Set Plane) < ∞) :
    (∫⁻ w : Plane, cellPairEnergyTransport K L a w z ∂volume)
      = interiorIndicator L z * ENNReal.ofReal a *
          ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) * (volume (L : Set Plane))⁻¹ := by
  have hI : MeasurableSet (interior (K : Set Plane)) := isOpen_interior.measurableSet
  have hw : ∀ w : Plane, cellPairEnergyTransport K L a w z
      = Set.indicator (interior (K : Set Plane))
        (fun _ => interiorIndicator L z * ENNReal.ofReal a *
          ENNReal.ofReal (Metric.diam (L : Set Plane) ^ 2) * (volume (L : Set Plane))⁻¹ *
          (volume (K : Set Plane))⁻¹) w := by
    intro w
    by_cases hwI : w ∈ interior (K : Set Plane)
    · rw [Set.indicator_of_mem hwI, cellPairEnergyTransport, interiorIndicator_of_mem hwI]
      ring
    · rw [Set.indicator_of_notMem hwI, cellPairEnergyTransport,
        interiorIndicator_of_notMem hwI]
      ring
  simp_rw [hw]
  rw [lintegral_indicator_const hI, volume_interior_eq_of_frontier_null hfrontK, mul_assoc,
    ENNReal.inv_mul_cancel hposK.ne' hfinK.ne, mul_one]

theorem lintegral_energyTransport_outgoing (e : Env) (w : Plane) :
    (∫⁻ z : Plane, energyTransport (e, w, z) ∂volume)
      = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          interiorIndicator ((decode e).cell v) w *
              ENNReal.ofReal ((decode e).graph.c v v') *
              ENNReal.ofReal (Metric.diam ((decode e).cell v' : Set Plane) ^ 2) *
            (volume ((decode e).cell v : Set Plane))⁻¹ := by
  have hgeom := decode_geometry e
  have hmeas : ∀ v v' : Vertex e.val, Measurable fun z : Plane =>
      cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
        ((decode e).graph.c v v') w z := fun v v' =>
    measurable_cellPairEnergyTransport_target _ _ _ _
  calc (∫⁻ z : Plane, energyTransport (e, w, z) ∂volume)
      = ∫⁻ z : Plane, ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z ∂volume :=
        lintegral_congr fun z => energyTransport_eq_tsum_vertex e w z
    _ = ∑' v : Vertex e.val, ∫⁻ z : Plane, ∑' v' : Vertex e.val,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z ∂volume :=
        lintegral_tsum fun v => (Measurable.ennreal_tsum fun v' => hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val, ∫⁻ z : Plane,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z ∂volume :=
        tsum_congr fun v => lintegral_tsum fun v' => (hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          interiorIndicator ((decode e).cell v) w *
              ENNReal.ofReal ((decode e).graph.c v v') *
              ENNReal.ofReal (Metric.diam ((decode e).cell v' : Set Plane) ^ 2) *
            (volume ((decode e).cell v : Set Plane))⁻¹ :=
        tsum_congr fun v => tsum_congr fun v' =>
          lintegral_cellPairEnergyTransport_target _ _ _ _ (hgeom.2.2.1 v')
            (cellVolume_pos_lt_top (decode e) hgeom v').1
            (cellVolume_pos_lt_top (decode e) hgeom v').2

theorem lintegral_energyTransport_incoming (e : Env) (z : Plane) :
    (∫⁻ w : Plane, energyTransport (e, w, z) ∂volume)
      = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          interiorIndicator ((decode e).cell v') z *
              ENNReal.ofReal ((decode e).graph.c v v') *
              ENNReal.ofReal (Metric.diam ((decode e).cell v' : Set Plane) ^ 2) *
            (volume ((decode e).cell v' : Set Plane))⁻¹ := by
  have hgeom := decode_geometry e
  have hmeas : ∀ v v' : Vertex e.val, Measurable fun w : Plane =>
      cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
        ((decode e).graph.c v v') w z := fun v v' =>
    measurable_cellPairEnergyTransport_source _ _ _ _
  calc (∫⁻ w : Plane, energyTransport (e, w, z) ∂volume)
      = ∫⁻ w : Plane, ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z ∂volume :=
        lintegral_congr fun w => energyTransport_eq_tsum_vertex e w z
    _ = ∑' v : Vertex e.val, ∫⁻ w : Plane, ∑' v' : Vertex e.val,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z ∂volume :=
        lintegral_tsum fun v => (Measurable.ennreal_tsum fun v' => hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val, ∫⁻ w : Plane,
          cellPairEnergyTransport ((decode e).cell v) ((decode e).cell v')
            ((decode e).graph.c v v') w z ∂volume :=
        tsum_congr fun v => lintegral_tsum fun v' => (hmeas v v').aemeasurable
    _ = ∑' v : Vertex e.val, ∑' v' : Vertex e.val,
          interiorIndicator ((decode e).cell v') z *
              ENNReal.ofReal ((decode e).graph.c v v') *
              ENNReal.ofReal (Metric.diam ((decode e).cell v' : Set Plane) ^ 2) *
            (volume ((decode e).cell v' : Set Plane))⁻¹ :=
        tsum_congr fun v => tsum_congr fun v' =>
          lintegral_cellPairEnergyTransport_source _ _ _ _ (hgeom.2.2.1 v)
            (cellVolume_pos_lt_top (decode e) hgeom v).1
            (cellVolume_pos_lt_top (decode e) hgeom v).2

/-- Off the boundary mask the outgoing integral from the origin is exactly the neighbour
weighted diameter density `a_{H_0}⁻¹ ∑_{H' ∼ H_0} c(H_0,H') d_{H'}²`. -/
theorem lintegral_energyTransport_outgoing_eq_rooted (e : Env)
    (he : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) :
    (∫⁻ z : Plane, energyTransport (e, 0, z) ∂volume)
      = rootedNeighborDiamSqDensity (decode e) 0 := by
  have hgeom := decode_geometry e
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) hgeom he
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode e) hgeom he
  have harea : ENNReal.ofReal (StatementIngredients.cellArea (decode e) v₀)
      = volume ((decode e).cell v₀ : Set Plane) := by
    rw [StatementIngredients.cellArea,
      ENNReal.ofReal_toReal (cellVolume_pos_lt_top (decode e) hgeom v₀).2.ne]
  have hone : interiorIndicator ((decode e).cell v₀) 0 = 1 := interiorIndicator_of_mem hint
  rw [lintegral_energyTransport_outgoing e 0]
  rw [tsum_eq_single v₀ ?_]
  · simp only [rootedNeighborDiamSqDensity, hv₀, Option.elim, neighborDiamSqDensity, harea,
      div_eq_mul_inv]
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun v' => by rw [hone, one_mul]
  · intro v hv
    have hnot : (0 : Plane) ∉ interior ((decode e).cell v : Set Plane) := by
      intro hmem
      exact hv (huniq.unique hmem hint)
    refine ENNReal.tsum_eq_zero.mpr fun v' => ?_
    rw [interiorIndicator_of_notMem hnot]
    simp

/-- Off the boundary mask the incoming integral at the origin is exactly the rooted
`d_{H_0}² π(H_0) / a_{H_0}`, by summing the conductance over all incoming neighbours. -/
theorem lintegral_energyTransport_incoming_eq_rooted (e : Env)
    (he : (0 : Plane) ∉ RootDensities.boundaryMask (decode e)) :
    (∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume)
      = rootedDiamSqPiDensity (decode e) 0 := by
  have hgeom := decode_geometry e
  obtain ⟨v₀, hv₀, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) hgeom he
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode e) hgeom he
  have harea : ENNReal.ofReal (StatementIngredients.cellArea (decode e) v₀)
      = volume ((decode e).cell v₀ : Set Plane) := by
    rw [StatementIngredients.cellArea,
      ENNReal.ofReal_toReal (cellVolume_pos_lt_top (decode e) hgeom v₀).2.ne]
  have hone : interiorIndicator ((decode e).cell v₀) 0 = 1 := interiorIndicator_of_mem hint
  have hinner : ∀ v : Vertex e.val,
      (∑' v' : Vertex e.val, interiorIndicator ((decode e).cell v') 0 *
          ENNReal.ofReal ((decode e).graph.c v v') *
          ENNReal.ofReal (Metric.diam ((decode e).cell v' : Set Plane) ^ 2) *
          (volume ((decode e).cell v' : Set Plane))⁻¹)
        = ENNReal.ofReal ((decode e).graph.c v v₀) *
            (ENNReal.ofReal (Metric.diam ((decode e).cell v₀ : Set Plane) ^ 2) *
              (volume ((decode e).cell v₀ : Set Plane))⁻¹) := by
    intro v
    rw [tsum_eq_single v₀ ?_]
    · rw [hone, one_mul, mul_assoc]
    · intro v' hv'
      have hnot : (0 : Plane) ∉ interior ((decode e).cell v' : Set Plane) := by
        intro hmem
        exact hv' (huniq.unique hmem hint)
      rw [interiorIndicator_of_notMem hnot]
      simp
  have hsymm : ∀ v : Vertex e.val,
      (decode e).graph.c v v₀ = (decode e).graph.c v₀ v := fun v =>
    (decode e).graph.c_symm v v₀
  rw [lintegral_energyTransport_incoming e 0, tsum_congr hinner, ENNReal.tsum_mul_right]
  simp only [rootedDiamSqPiDensity, hv₀, Option.elim, diamSqPiDensity, harea, div_eq_mul_inv]
  rw [tsum_congr fun v : Vertex e.val => congrArg ENNReal.ofReal (hsymm v),
    ← ofReal_pi_eq_tsum]
  ring

/-! ### The manuscript mass transport step -/

/-! ### `s:lem:e0`: `e_0 ≤ 2 M_π < ∞` -/

/-- The manuscript specific energy `e_0 = ‖∇b‖_*²` of the base (centroid) embedding. -/
noncomputable def baseSpecificEnergy (ν : Measure Env) : ℝ≥0∞ :=
  ∫⁻ e : Env, RootDensities.rootedSpecificEnergyDensity (decode e)
    (StatementIngredients.cellCentroid (decode e)) 0 ∂ν

/-- The manuscript moment `M_π = E[d_{H_0}² π(H_0) / a_{H_0}]`. -/
noncomputable def diamSqPiMoment (ν : Measure Env) : ℝ≥0∞ :=
  ∫⁻ e : Env, rootedDiamSqPiDensity (decode e) 0 ∂ν

/-- `M_π` is finite under the manuscript finite-energy moment hypothesis (FE). -/
theorem diamSqPiMoment_lt_top (ν : Measure Env)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    diamSqPiMoment ν < ∞ :=
  lt_of_le_of_lt
    (lintegral_mono fun e => rootedDiamSqPiDensity_le_rootedFiniteEnergyDensity (decode e) 0)
    hFE.lt_top

/-- **`e_0 ≤ 2 M_π`.**  The deterministic centroid bound plus the mass-transport identity for
the manuscript edge transport. -/
theorem baseSpecificEnergy_le_two_mul_diamSqPiMoment (ν : Measure Env) (hν : MassTransport ν) :
    baseSpecificEnergy ν ≤ 2 * diamSqPiMoment ν := by
  have hHmeas : Measurable fun e : Env => ∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume :=
    energyTransportKernel.measurable_incoming.lintegral_prod_right'
  have hroot := ae_notMem_boundaryMask_of_massTransport ν hν
  have hstep1 : baseSpecificEnergy ν
      ≤ ∫⁻ e : Env, ((∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume) +
          ∫⁻ z : Plane, energyTransport (e, 0, z) ∂volume) ∂ν := by
    rw [baseSpecificEnergy]
    refine lintegral_mono_ae ?_
    filter_upwards [hroot] with e he
    rw [lintegral_energyTransport_incoming_eq_rooted e he,
      lintegral_energyTransport_outgoing_eq_rooted e he]
    exact rootedSpecificEnergyDensity_cellCentroid_le (decode e) (decode_geometry e) 0
  have hstep2 : (∫⁻ e : Env, ((∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume) +
        ∫⁻ z : Plane, energyTransport (e, 0, z) ∂volume) ∂ν)
      = (∫⁻ e : Env, ∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume ∂ν) +
        ∫⁻ e : Env, ∫⁻ z : Plane, energyTransport (e, 0, z) ∂volume ∂ν :=
    lintegral_add_left hHmeas _
  have hstep3 : (∫⁻ e : Env, ∫⁻ z : Plane, energyTransport (e, 0, z) ∂volume ∂ν)
      = ∫⁻ e : Env, ∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume ∂ν :=
    hν energyTransportKernel
  have hstep4 : (∫⁻ e : Env, ∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume ∂ν)
      = diamSqPiMoment ν := by
    rw [diamSqPiMoment]
    refine lintegral_congr_ae ?_
    filter_upwards [hroot] with e he
    exact lintegral_energyTransport_incoming_eq_rooted e he
  calc baseSpecificEnergy ν
      ≤ (∫⁻ e : Env, ∫⁻ w : Plane, energyTransport (e, w, 0) ∂volume ∂ν) +
          ∫⁻ e : Env, ∫⁻ z : Plane, energyTransport (e, 0, z) ∂volume ∂ν :=
        hstep1.trans_eq hstep2
    _ = diamSqPiMoment ν + diamSqPiMoment ν := by rw [hstep3, hstep4]
    _ = 2 * diamSqPiMoment ν := (two_mul _).symm

/-- **The base embedding has finite specific energy (`s:lem:e0`).**  With
`M_π = E[d_{H_0}² π(H_0)/a_{H_0}]`, the specific energy of the centroid (base) embedding
satisfies `e_0 ≤ 2 M_π < ∞`. -/
theorem baseSpecificEnergy_le_two_mul_diamSqPiMoment_lt_top (ν : Measure Env)
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞) :
    baseSpecificEnergy ν ≤ 2 * diamSqPiMoment ν ∧ 2 * diamSqPiMoment ν < ∞ := by
  refine ⟨baseSpecificEnergy_le_two_mul_diamSqPiMoment ν hν, ?_⟩
  exact (ENNReal.mul_ne_top (by simp) (diamSqPiMoment_lt_top ν hFE).ne).lt_top

end ReflectedGMS.BaseSpecificEnergy

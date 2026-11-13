/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GeometricMassQuadraticProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedCentroidSublinearityProducer
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureSpatialDiameterBounds
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureCutoffBounds
import LatticeProb.Bonanno.ReflectedGMS.Process.LocalAreaSummability

/-!
# `s:eq:Wbound` in the quadratic form, discharged

`Corrector/MarkedCentroidSublinearityProducer` discharges the centroid half `hsub` of the
harmonic-coordinate assembly from two open inputs: `MarkedGeometricMassQuadratic`
(`s:eq:Wbound` in the quadratic form `W(R) ≤ K R²`) and `MarkedSmallBlockResidual`
(`s:eq:smallresidual`).  This module removes the **first** one, from the manuscript's own
`s:eq:MTP` and finite (FE) moment and nothing else.

Its docstring named the missing step exactly: "the comparison of the `ℝ≥0∞`-valued
`reciprocalConductanceMass` with the real `piStar`".  That comparison is an *identity*, not an
inequality:

* `reciprocalConductance_eq_ofReal` — off the edge set the `ℝ≥0∞` reciprocal conductance is
  `0` and `(c H H')⁻¹ = 0⁻¹ = 0` in `ℝ`, while on the edge set `c > 0`
  (`ReflectedWalk.ConductanceGraph.Adj` *is* `0 < c`) so `ENNReal.ofReal_inv_of_pos` applies.
  Hence `reciprocalConductance G (v, w) = ENNReal.ofReal (G.c v w)⁻¹` with no side condition.
* `reciprocalConductanceMass_eq_ofReal_piStar` — `Geometry`'s local finiteness makes
  `w ↦ (c v w)⁻¹` finitely supported, hence summable, so `ENNReal.ofReal_tsum_of_nonneg`
  turns the real `π*(H)` into the `ℝ≥0∞` mass.  This is the same finite-support remark that
  `Environment/RootDensities` makes in prose about `piStar`.

Everything else is reuse:

* `AlmostSureSpatialDiameterBounds.volume_mul_finiteEnergyDensity_eq` — `a_H ρ_FE(H)
  = d_H² (π_H + π*_H)`;
* `AlmostSureCutoffBounds.tsum_cellDensity_le_setLIntegral` — `∑_{H ∈ A} a_H g(H) ≤ ∫_B g(H_z)`
  whenever every cell of `A` lies in `B`;
* `Process/LocalAreaSummability.cell_subset_closedBall_add_maxDiamHittingBall_toReal` — a cell
  meeting `B̄_R` lies in `B̄_{R + D_R}`;
* `Spatial.ae_maxDiamHittingBall_finite_and_sublinear` (`s:eq:DR`) — `D_R < ∞` and
  `D_R = o(R)`, so `D_R ≤ R` for all large `R` and `(R + D_R)² ≤ 4 R²`;
* `Spatial/SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity`
  (`s:prop:maximal`) — `∫_{B̄_r} ρ_FE ≤ r² M` with `M < ∞` almost surely.

The explicit constant is `K = 4 M`, with `M` the environment's own maximal constant.  Note
that this is *strictly stronger* than the finite-radius half
`PatchCentroidTraceFiniteEnergy.SpatialDiameterCellBounds` discharged by
`Spatial/SpatialMaximalForFiniteEnergy.ae_spatialDiameterCellBounds`, which only asserts
summability at each radius and carries no constant.

Combined with `Corrector/SmallBlockResidualProducer`, the consequence is that `hsub`
(`MarkedCentroidSublinearity`) now rests on the single open input
`SmallBlockResidualProducer.MarkedResidualWeakMaximal` — the manuscript's weak-`L¹` maximal
inequality `s:eq:maximal` applied to the residual density — together with inputs the assembly
already takes.  The final statements are still implications; they do not prove the
harmonic-coordinate theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.GeometricMassQuadraticProducer

open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation HarmonicMainStatement
open HarmonicCoordinateAssembly CentroidSublinearityFromResidual
open MarkedCentroidSublinearityProducer

variable {V : Type*} [Countable V]

/-! ### The `ℝ≥0∞` reciprocal conductance is the `ofReal` of the real one -/

/-- **The comparison the producer's docstring asked for, as an identity.**  Off the edge set
both sides vanish, because `¬ Adj v w` means `c v w = 0` and `(0 : ℝ)⁻¹ = 0`; on the edge set
`c v w > 0`, so `ENNReal.ofReal` commutes with the inverse. -/
theorem reciprocalConductance_eq_ofReal (G : ReflectedWalk.ConductanceGraph V) (v w : V) :
    reciprocalConductance G (v, w) = ENNReal.ofReal (G.c v w)⁻¹ := by
  unfold reciprocalConductance
  split_ifs with h
  · have hpos : (0 : ℝ) < G.c v w := h
    exact (ENNReal.ofReal_inv_of_pos hpos).symm
  · have hnpos : ¬ (0 : ℝ) < G.c v w := h
    have hzero : G.c v w = 0 := le_antisymm (not_lt.1 hnpos) (G.c_nonneg v w)
    simp [hzero]

/-- The reciprocal-conductance sum `w ↦ (c v w)⁻¹` is finitely supported, by `Geometry`'s
local finiteness, hence summable. -/
theorem summable_inv_conductance (F : IndexedCells V) (hF : Geometry F) (v : V) :
    Summable fun w : V => (F.graph.c v w)⁻¹ := by
  classical
  have hfin : (F.graph.toSimpleGraph.neighborSet v).Finite := hF.2.2.2.2.2.2.1 v
  refine summable_of_ne_finset_zero (s := hfin.toFinset) ?_
  intro w hw
  have hadj : ¬ F.graph.toSimpleGraph.Adj v w := fun h => hw (hfin.mem_toFinset.2 h)
  have hnpos : ¬ (0 : ℝ) < F.graph.c v w := hadj
  have hzero : F.graph.c v w = 0 := le_antisymm (not_lt.1 hnpos) (F.graph.c_nonneg v w)
  simp [hzero]

/-- **`π*(H)` in `ℝ≥0∞` is the `ofReal` of `π*(H)` in `ℝ`.** -/
theorem reciprocalConductanceMass_eq_ofReal_piStar (F : IndexedCells V) (hF : Geometry F)
    (v : V) :
    reciprocalConductanceMass F.graph v = ENNReal.ofReal (RootDensities.piStar F v) := by
  rw [RootDensities.piStar,
    ENNReal.ofReal_tsum_of_nonneg (fun w => inv_nonneg.2 (F.graph.c_nonneg v w))
      (summable_inv_conductance F hF v)]
  exact tsum_congr fun w => reciprocalConductance_eq_ofReal F.graph v w

/-! ### The cell diameter in `ℝ≥0∞` -/

/-- Cells are compact, so their extended diameter is the `ofReal` of their diameter. -/
theorem cellDiameter_eq_ofReal (F : IndexedCells V) (v : V) :
    cellDiameter F v = ENNReal.ofReal (Metric.diam (F.cell v : Set Plane)) := by
  have hbdd : Bornology.IsBounded (F.cell v : Set Plane) := (F.cell v).isCompact.isBounded
  have hdiam : Metric.diam (F.cell v : Set Plane)
      = (Metric.ediam (F.cell v : Set Plane)).toReal := rfl
  rw [cellDiameter, hdiam, ENNReal.ofReal_toReal hbdd.ediam_ne_top]

/-! ### The summand of `W` is below the (FE) cell mass -/

/-- **`d_H² π*(H) ≤ a_H ρ_FE(H)`**, because `ρ_FE` carries `π + π*` and `π ≥ 0`. -/
theorem cellMass_le_volume_mul_finiteEnergyDensity (F : IndexedCells V) (hF : Geometry F)
    (v : V) :
    cellDiameter F v ^ (2 : ℝ) * reciprocalConductanceMass F.graph v
      ≤ volume ((F.cell v : Set Plane)) * RootDensities.finiteEnergyDensity F v := by
  have hd : (0 : ℝ) ≤ Metric.diam (F.cell v : Set Plane) := Metric.diam_nonneg
  have hpi : (0 : ℝ) ≤ RootDensities.pi F v := F.graph.pi_nonneg v
  rw [AlmostSureSpatialDiameterBounds.volume_mul_finiteEnergyDensity_eq F hF v,
    cellDiameter_eq_ofReal F v, ENNReal.rpow_two, ← ENNReal.ofReal_pow hd,
    reciprocalConductanceMass_eq_ofReal_piStar F hF v,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Metric.diam (F.cell v : Set Plane) ^ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle : RootDensities.piStar F v
      ≤ RootDensities.pi F v + RootDensities.piStar F v := by linarith
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- **`W` on a patch is below the rooted (FE) integral over any set containing its cells.** -/
theorem patchMass_le_setLIntegral (F : IndexedCells V) (hF : Geometry F)
    {A : Set V} {B : Set Plane} (hAB : ∀ v ∈ A, (F.cell v : Set Plane) ⊆ B) :
    patchDiameterReciprocalConductanceMass F A
      ≤ ∫⁻ z in B, RootDensities.rootedFiniteEnergyDensity F z ∂volume := by
  have h1 : (∑' v : A, cellDiameter F v.1 ^ (2 : ℝ) * reciprocalConductanceMass F.graph v.1)
      ≤ ∑' v : A, volume ((F.cell v.1 : Set Plane)) * RootDensities.finiteEnergyDensity F v.1 :=
    ENNReal.tsum_le_tsum fun v => cellMass_le_volume_mul_finiteEnergyDensity F hF v.1
  exact le_trans h1 (AlmostSureCutoffBounds.tsum_cellDensity_le_setLIntegral F hF
    (RootDensities.finiteEnergyDensity F) hAB)

/-- **`W(R)` from a ball bound on the rooted (FE) density.** -/
theorem patchMass_hittingBall_le (F : IndexedCells V) (hF : Geometry F) {R : ℝ} (hR : 0 ≤ R)
    (hD : Spatial.maxDiamHittingBall F R < ∞) {M : ℝ≥0∞}
    (hb : ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity F x ∂volume) ≤ ENNReal.ofReal (r ^ 2) * M)
    (hpos : 0 < R + (Spatial.maxDiamHittingBall F R).toReal) :
    patchDiameterReciprocalConductanceMass F
        (hittingVertices F (Metric.closedBall (0 : Plane) R))
      ≤ ENNReal.ofReal ((R + (Spatial.maxDiamHittingBall F R).toReal) ^ 2) * M := by
  refine le_trans (patchMass_le_setLIntegral F hF
    (B := Metric.closedBall (0 : Plane) (R + (Spatial.maxDiamHittingBall F R).toReal))
    ?_) (hb _ hpos)
  intro v hv
  exact cell_subset_closedBall_add_maxDiamHittingBall_toReal F hR hD ⟨v, hv⟩

/-! ### The elementary radius arithmetic -/

theorem sq_add_le_four_mul_sq {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (hDR : D ≤ R) :
    (R + D) ^ 2 ≤ 4 * R ^ 2 := by nlinarith

/-! ### `s:eq:Wbound`, quadratic form, almost surely -/

/-- **`MarkedGeometricMassQuadratic` discharged.**  Almost every environment carries a single
constant `K = 4 M` with `W(R) ≤ K R²` at every large radius, from the manuscript's own
`s:eq:MTP` and finite (FE) moment: `s:prop:maximal` supplies `M`, and `s:eq:DR` makes the
enlargement `R ↦ R + D_R` at most a doubling. -/
theorem markedGeometricMassQuadratic_of_massTransport (ν : Measure Env)
    [IsProbabilityMeasure ν] (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    MarkedGeometricMassQuadratic ν := by
  have hgeo := Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE.ne
  have hmax :=
    SpatialMaximalForFiniteEnergy.ae_exists_ballBound_rootedFiniteEnergyDensity ν hν hFE.ne
  have key : ∀ᵐ e : Env ∂ν, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ R : ℝ in atTop,
      patchDiameterReciprocalConductanceMass (decode e)
          (hittingVertices (decode e) (Metric.closedBall (0 : Plane) R))
        ≤ ENNReal.ofReal (K * R ^ 2) := by
    filter_upwards [hgeo, hmax] with e he hm
    obtain ⟨M, hMtop, hb⟩ := hm
    obtain ⟨R₀, hR₀pos, hR₀⟩ := he.2.1 1 one_pos
    refine ⟨4 * M.toReal, by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (max R₀ 1)] with R hR
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_right R₀ 1) hR
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
    have hR0R : R₀ ≤ R := le_trans (le_max_left R₀ 1) hR
    have hDfin : Spatial.maxDiamHittingBall (decode e) R < ∞ := he.1 R hRpos.le
    have hDle : Spatial.maxDiamHittingBall (decode e) R ≤ ENNReal.ofReal R := by
      have h := hR₀ R hR0R
      rwa [one_mul] at h
    have hDtoReal : (Spatial.maxDiamHittingBall (decode e) R).toReal ≤ R :=
      ENNReal.toReal_le_of_le_ofReal hRpos.le hDle
    have hDnn : (0 : ℝ) ≤ (Spatial.maxDiamHittingBall (decode e) R).toReal :=
      ENNReal.toReal_nonneg
    have hsum : (0 : ℝ) < R + (Spatial.maxDiamHittingBall (decode e) R).toReal := by linarith
    have hsq : (R + (Spatial.maxDiamHittingBall (decode e) R).toReal) ^ 2 ≤ 4 * R ^ 2 :=
      sq_add_le_four_mul_sq hRpos.le hDnn hDtoReal
    refine le_trans
      (patchMass_hittingBall_le (decode e) (decode_geometry e) hRpos.le hDfin hb hsum) ?_
    calc ENNReal.ofReal ((R + (Spatial.maxDiamHittingBall (decode e) R).toReal) ^ 2) * M
        ≤ ENNReal.ofReal (4 * R ^ 2) * M :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hsq) le_rfl
      _ = ENNReal.ofReal (4 * R ^ 2) * ENNReal.ofReal M.toReal := by
          rw [ENNReal.ofReal_toReal hMtop]
      _ = ENNReal.ofReal (4 * R ^ 2 * M.toReal) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (4 * M.toReal * R ^ 2) := by
          congr 1
          ring
  exact key

end ReflectedGMS.GeometricMassQuadraticProducer

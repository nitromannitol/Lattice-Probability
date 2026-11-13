/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.AlmostSureSpatialDiameterBounds at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.AlmostSureCutoffBounds
import LatticeProb.Bonanno.ReflectedGMS.Process.LocalAreaSummability
import LatticeProb.Bonanno.ReflectedGMS.Corrector.PatchCentroidTraceFiniteEnergy

/-!
# `s:cor:spatialbounds`, finite-radius half: an almost-sure producer of `s:eq:Wbound`

This module formalises the manuscript's own derivation of Corollary `s:cor:spatialbounds`
from Proposition `s:prop:maximal`, in the exact shape consumed by
`Corrector/PatchCentroidTraceFiniteEnergy` and `Corrector/SmallBlocksNonmacroscopic`:

`SpatialDiameterCellBounds F : ∀ R, Summable (fun v ∈ 𝓗(B̄_R) => d_v² (π_v + π*_v))`,

i.e. the finite-radius half `W(R) < ∞` of `s:eq:Wbound`.  The large-scale half
`limsup W(R)/R² < ∞` is *not* asserted here; no consumer of `SpatialDiameterCellBounds`
uses it.

## The manuscript's derivation, verbatim

`s:cor:spatialbounds` applies the spatial maximal inequality to

`F_q(𝓗) = d_{H_0}²(π(H_0) + π*(H_0)) / a_{H_0}`,  `ρ_q(z) = F_q(𝓗 − z)`,

which is exactly `RootDensities.rootedFiniteEnergyDensity`, the integrand of the
manuscript's own moment hypothesis (FE).  Every cell meeting `B̄_R` lies in `B̄_{R+D_R}`,
and integrating `ρ_q` there counts its entire weight, so `W(R) ≤ ∫_{B̄_{R+D_R}} ρ_q`.

Both geometric steps are already checked in this project and are reused, not redone:

* `Process/LocalAreaSummability.cell_subset_closedBall_add_maxDiamHittingBall_toReal` is the
  containment `H ⊆ B̄_{R+D_R}`, and `Spatial.ae_maxDiamHittingBall_finite_and_sublinear`
  supplies `D_R < ∞` almost surely from `MassTransport ν` and (FE) alone — this is
  `s:eq:DR` of `s:lem:largecells`;
* `Spatial/AlmostSureCutoffBounds.tsum_cellDensity_le_setLIntegral` is the cellwise-to-Lebesgue
  transfer `∑_{H ∈ A} a_H g(H) ≤ ∫_B g(H_z) dz`.

The only new deterministic content is `volume_mul_finiteEnergyDensity_eq`: the transfer is
applied to `g = RootDensities.finiteEnergyDensity` and

`a_H · ρ_FE(H) = d_H² (π_H + π*_H)`   **exactly**,

the areas cancelling because `Geometry F` makes every cell area positive and finite.  This
is where the `π*` half is recovered: the (FE) density already carries `π + π*`, so this
route produces the literal `W` of `s:eq:Wbound` and not only its `π`-part.  (The existing
`localMassENN` route of `AlmostSureCutoffBounds` discards `π*` by an inequality and can
therefore only yield `SpatialDiameterPiBounds`.)

## The single remaining input, stated plainly

The results below are **conditional**, on one hypothesis and nothing else:

`hloc : ∀ᵐ e ∂ν, ∀ r, ∫_{B̄_r} ρ_FE(𝓗_e) < ∞`,

the *local integrability* clause of manuscript Proposition `s:prop:maximal` ("the density
`ρ_ω(z) = F(ω − z)` is locally integrable almost surely").  It is strictly weaker than the
quadratic maximal bound `M(ρ) < ∞` that `s:prop:maximal` also asserts, and
`ae_spatialDiameterCellBounds_of_ballBound` derives it from that stronger form — which is
verbatim the hypothesis `hMax` already carried by
`Spatial/AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses` and by
`Recurrence/QuenchedFormulation.ae_quenchedWalkConclusion_of_massTransport`.

So this module does not create a new obligation: it *identifies* the corrector lane's
open hypothesis `hW` with the recurrence lane's open hypothesis `hMax`, and a single future
producer of `s:prop:maximal` discharges both.  At the time of writing `s:prop:maximal` has
no producer: `SpatialMaximalInequality.ballMaximal_lt_top_ae` still carries
`OriginChainRegular`, `BlockData` and `EnvironmentGrid`, and those three structures occur
nowhere in the project except as their own definitions and as hypotheses.

Local integrability is *not* obtainable from `MassTransport ν` and (FE) by a single
transport: mass transport modulo scaling (`s:eq:Tcov`) admits only kernels of exact degree
`−2` under every translation *and* dilation, so a fixed-radius ball kernel is inadmissible,
and every admissible kernel whose outgoing integral is bounded by a multiple of the (FE)
integrand puts a scale profile on the incoming side that degenerates on the small cells.
The manuscript's dyadic block martingale is what removes that degeneration.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.AlmostSureSpatialDiameterBounds

open Code EnvironmentLaws PatchCentroidTraceFiniteEnergy

variable {V : Type*} [Countable V]

/-! ### One cell: the area cancels exactly -/

/-- **`a_H · ρ_FE(H) = d_H² (π_H + π*_H)`.**  The manuscript's (FE) integrand
`(d_H²/a_H)(π_H + π*_H)`, multiplied by the cell area, returns the exact summand of the
manuscript quantity `W` of `s:eq:Wbound`.  `Geometry F` makes the cell area positive and
finite, so the cancellation is an identity, not an inequality.

This sharpens `AlmostSureCutoffBounds.ofReal_diamSq_mul_pi_le_volume_mul_finiteEnergyDensity`,
which discards `π*`; the two share the area-cancellation computation. -/
theorem volume_mul_finiteEnergyDensity_eq (F : IndexedCells V) (hF : Geometry F) (v : V) :
    volume ((F.cell v : Set Plane)) * RootDensities.finiteEnergyDensity F v
      = ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2 *
          (RootDensities.pi F v + RootDensities.piStar F v)) := by
  have hvol := cellVolume_pos_lt_top F hF v
  have hA : volume ((F.cell v : Set Plane))
      = ENNReal.ofReal (StatementIngredients.cellArea F v) :=
    (ENNReal.ofReal_toReal hvol.2.ne).symm
  have hne0 : ENNReal.ofReal (StatementIngredients.cellArea F v) ≠ 0 := fun h =>
    absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 (StatementIngredients.cellArea_pos F hF v))
  have hnet : ENNReal.ofReal (StatementIngredients.cellArea F v) ≠ ∞ := ENNReal.ofReal_ne_top
  have hpinn : (0 : ℝ) ≤ RootDensities.pi F v := F.graph.pi_nonneg v
  have hkey : volume ((F.cell v : Set Plane)) * RootDensities.finiteEnergyDensity F v
      = ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
          (ENNReal.ofReal (RootDensities.pi F v) +
            ENNReal.ofReal (RootDensities.piStar F v)) := by
    rw [hA]
    unfold RootDensities.finiteEnergyDensity
    rw [div_eq_mul_inv,
      show ENNReal.ofReal (StatementIngredients.cellArea F v) *
          (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹ *
            (ENNReal.ofReal (RootDensities.pi F v) +
              ENNReal.ofReal (RootDensities.piStar F v)))
        = (ENNReal.ofReal (StatementIngredients.cellArea F v) *
              (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹) *
            (ENNReal.ofReal (Metric.diam (F.cell v : Set Plane) ^ 2) *
              (ENNReal.ofReal (RootDensities.pi F v) +
                ENNReal.ofReal (RootDensities.piStar F v))) from by ring,
      ENNReal.mul_inv_cancel hne0 hnet, one_mul]
  rw [hkey, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_add hpinn (RootDensities.piStar_nonneg F v)]

/-! ### The local mass from a finite rooted-density integral -/

/-- **The manuscript's local mass is finite on any family of cells contained in a set of
finite rooted (FE) integral.**  `∑_{H ∈ A} d_H²(π_H + π*_H) ≤ ∫_B ρ_FE < ∞` whenever every
cell of `A` lies in `B`.  This is the display of `s:cor:spatialbounds`. -/
theorem localDiameterCellMass_of_setLIntegral_ne_top (F : IndexedCells V) (hF : Geometry F)
    {A : Set V} {B : Set Plane}
    (hAB : ∀ v ∈ A, (F.cell v : Set Plane) ⊆ B)
    (hB : (∫⁻ z in B, RootDensities.rootedFiniteEnergyDensity F z ∂volume) ≠ ∞) :
    LocalDiameterCellMass F A := by
  have hgen := AlmostSureCutoffBounds.tsum_cellDensity_le_setLIntegral F hF
    (RootDensities.finiteEnergyDensity F) hAB
  have hcongr : ∀ v : A,
      volume ((F.cell v.1 : Set Plane)) * RootDensities.finiteEnergyDensity F v.1
        = ENNReal.ofReal (Metric.diam (F.cell v.1 : Set Plane) ^ 2 *
            (RootDensities.pi F v.1 + RootDensities.piStar F v.1)) :=
    fun v => volume_mul_finiteEnergyDensity_eq F hF v.1
  have hsum : (∑' v : A, ENNReal.ofReal (Metric.diam (F.cell v.1 : Set Plane) ^ 2 *
      (RootDensities.pi F v.1 + RootDensities.piStar F v.1))) ≠ ∞ := by
    refine ne_top_of_le_ne_top hB ?_
    rw [← tsum_congr hcongr]
    exact hgen
  have hfin : Summable (fun v : A => Metric.diam (F.cell v.1 : Set Plane) ^ 2 *
      (RootDensities.pi F v.1 + RootDensities.piStar F v.1)) := by
    refine (ENNReal.summable_toReal hsum).congr ?_
    intro v
    exact ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
      (add_nonneg (F.graph.pi_nonneg v.1) (RootDensities.piStar_nonneg F v.1)))
  exact hfin

/-! ### `s:eq:Wbound` at every radius, deterministically -/

/-- **Corollary `s:cor:spatialbounds`, finite-radius half, pathwise.**  From `D_R < ∞` at
every nonnegative radius (`s:eq:DR`) and local integrability of the rooted (FE) density
(the first clause of `s:prop:maximal`), the manuscript's `W(R)` is finite at every radius.

Negative radii are covered because `B̄_R ⊆ B̄_{max R 0}`. -/
theorem spatialDiameterCellBounds_of_locallyIntegrable (F : IndexedCells V) (hF : Geometry F)
    (hD : ∀ R : ℝ, 0 ≤ R → Spatial.maxDiamHittingBall F R < ∞)
    (hloc : ∀ r : ℝ, (∫⁻ z in Metric.closedBall (0 : Plane) r,
      RootDensities.rootedFiniteEnergyDensity F z ∂volume) ≠ ∞) :
    SpatialDiameterCellBounds F := by
  intro R
  have hS : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hsub : {v : V | Hits F (Metric.closedBall (0 : Plane) R) v}
      ⊆ {v : V | Hits F (Metric.closedBall (0 : Plane) (max R 0)) v} := fun _ hv =>
    hits_mono F (Metric.closedBall_subset_closedBall (le_max_left R 0)) hv
  refine localDiameterCellMass_mono F hsub ?_
  refine localDiameterCellMass_of_setLIntegral_ne_top F hF
    (B := Metric.closedBall (0 : Plane)
      (max R 0 + (Spatial.maxDiamHittingBall F (max R 0)).toReal)) ?_ (hloc _)
  intro v hv
  exact cell_subset_closedBall_add_maxDiamHittingBall_toReal F hS (hD _ hS) ⟨v, hv⟩

/-! ### The almost-sure statements -/

/-- **`s:eq:Wbound` almost surely, from the local-integrability clause of `s:prop:maximal`.**

Besides the manuscript's own `MassTransport ν` and the finite (FE) moment — which supply
`s:eq:DR` through the checked `Spatial.ae_maxDiamHittingBall_finite_and_sublinear` — the only
hypothesis is `hloc`, almost-sure local integrability of the rooted (FE) density.  That is
the first conclusion of manuscript Proposition `s:prop:maximal`; it has no producer in the
project at the time of writing, so this theorem is honestly **conditional on
`s:prop:maximal`, and on nothing else**. -/
theorem ae_spatialDiameterCellBounds_of_ae_locallyIntegrable (ν : Measure Env)
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hloc : ∀ᵐ e ∂ν, ∀ r : ℝ, (∫⁻ z in Metric.closedBall (0 : Plane) r,
      RootDensities.rootedFiniteEnergyDensity (decode e) z ∂volume) ≠ ∞) :
    ∀ᵐ e ∂ν, SpatialDiameterCellBounds (decode e) := by
  filter_upwards [Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE, hloc]
    with e he hl
  exact spatialDiameterCellBounds_of_locallyIntegrable (decode e) (decode_geometry e) he.1 hl

/-- A finite maximal constant for the ball averages gives local integrability at every
radius: the positive radii are the hypothesis itself, and every nonpositive radius is
absorbed into radius `1`. -/
theorem locallyIntegrable_of_ballBound {F : IndexedCells V} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hb : ∀ r : ℝ, 0 < r → (∫⁻ x in Metric.closedBall (0 : Plane) r,
      RootDensities.rootedFiniteEnergyDensity F x ∂volume) ≤ ENNReal.ofReal (r ^ 2) * M) :
    ∀ r : ℝ, (∫⁻ z in Metric.closedBall (0 : Plane) r,
      RootDensities.rootedFiniteEnergyDensity F z ∂volume) ≠ ∞ := by
  intro r
  rcases le_or_gt r 0 with hr | hr
  · refine ne_top_of_le_ne_top ?_
      (lintegral_mono_set (Metric.closedBall_subset_closedBall (by linarith : r ≤ 1)))
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) (hb 1 one_pos)
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM) (hb r hr)

/-- **`s:eq:Wbound` almost surely, from the quadratic maximal bound of `s:prop:maximal`.**

The hypothesis `hMax` here is *verbatim* the one already carried by
`Spatial/AlmostSureCutoffBounds.ae_exists_logCutoff_hypotheses` and by
`Recurrence/QuenchedFormulation.ae_quenchedWalkConclusion_of_massTransport`: almost every
environment admits a finite random maximal constant `M` with `∫_{B̄_r} ρ_FE ≤ r² M` at every
positive radius.  So the corrector lane's open hypothesis `hW` and the recurrence lane's
open hypothesis `hMax` are the *same* obligation, namely `s:prop:maximal`. -/
theorem ae_spatialDiameterCellBounds_of_ballBound (ν : Measure Env) (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, RootDensities.rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (hMax : ∀ᵐ e ∂ν, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ x in Metric.closedBall (0 : Plane) r,
        RootDensities.rootedFiniteEnergyDensity (decode e) x ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M) :
    ∀ᵐ e ∂ν, SpatialDiameterCellBounds (decode e) := by
  refine ae_spatialDiameterCellBounds_of_ae_locallyIntegrable ν hν hFE ?_
  filter_upwards [hMax] with e he
  obtain ⟨M, hMtop, hb⟩ := he
  exact locallyIntegrable_of_ballBound hMtop hb

end ReflectedGMS.AlmostSureSpatialDiameterBounds

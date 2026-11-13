/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.AreaClockAdmissibleDischarge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClockFastSpeedOccupation
import LatticeProb.Bonanno.ReflectedGMS.Spatial.SpatialMaximalForFiniteEnergy

/-!
# `EnvironmentAreaClockAdmissible` discharged: `hdata` from the main theorem's own hypotheses

`EnvironmentWalkDataProducer.EnvironmentAreaClockAdmissible` was the sole open input behind
the `hdata` clause of the invariance assembly.
`AreaClockFastSpeedOccupation.environmentAreaClockAdmissible_of_geometry` reduced it,
per environment, to `AreaClockFastSpeedOccupation.EnvironmentAreaClockGeometry`, i.e. to

* a choice of cell representatives `zrep` (`CellRepresentatives`),
* `D_R < ∞` for every radius (`Spatial.maxDiamHittingBall`), and
* vanishing far-field energy at every root for the radius `‖zrep ·‖`
  (`ExcursionBoundedRange.VanishingFarEnergy`).

This file proves all three almost surely from **mass transport and the finite (FE) moment
alone** — the main theorem's own environment hypotheses — and hence discharges `hdata`.

* **Representatives** exist for *every* environment: cells are `NonemptyCompacts`, so a point
  can be chosen in each (`exists_cellRepresentatives`).  No measurability of the choice is
  needed, because the clock clause is a per-environment statement.
* **`D_R < ∞`** is the first clause of the checked large-cell decay
  `Spatial.ae_maxDiamHittingBall_finite_and_sublinear`.
* **Vanishing far energy** is manuscript Proposition `r:prop:log` in the adapter form
  `LogCutoffSpatialBoundedness.vanishingFarEnergy_norm_of_logCutoff`, whose hypothesis tuple
  `(r₀, C, hD, hW)` is supplied — simultaneously for *every* choice of representatives and of
  root — by `SpatialMaximalForFiniteEnergy.ae_exists_logCutoff_hypotheses`, i.e. by the checked
  spatial maximal inequality `s:prop:maximal` for the rooted (FE) density.

`environmentAreaClockGeometry_of_logCutoff` is the deterministic, per-environment step;
`ae_environmentAreaClockAdmissible` is the discharge of the residual, and
`reflectedInvarianceConclusions_of_named_inputs_hdata_discharged` is main theorem 2's reduction
with `hdata` (and `hclock`, and the recurrence input) removed.  It is an implication, not a
proof of the reflected invariance principle: `hΦ`, `hlift`, `hbracket`, `hlimit` stay open.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.AreaClockAdmissibleDischarge

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.InvarianceAssemblyNoReturn ReflectedGMS.AreaClockLevelZeroFiniteness
open ReflectedGMS.AreaClockFastSpeedOccupation

/-! ## Cell representatives exist unconditionally -/

/-- **Every indexed cell family admits cell representatives.**  Cells are nonempty compact
sets (`TopologicalSpace.NonemptyCompacts`), so a point can be chosen in each; no geometry
hypothesis is needed. -/
theorem exists_cellRepresentatives {V : Type*} (F : IndexedCells V) :
    ∃ z : V → Plane, CellRepresentatives F z :=
  ⟨fun v => (F.cell v).nonempty.some, fun v => (F.cell v).nonempty.some_mem⟩

/-! ## The per-environment step -/

/-- **The geometric inputs of the occupation route, for one environment, from `D_R < ∞` and
the hypothesis tuple of Proposition `r:prop:log`.**  The tuple is taken in the exact form
produced by `SpatialMaximalForFiniteEnergy.ae_exists_logCutoff_hypotheses`: for every choice of
representatives and every root.  Representatives are chosen by `exists_cellRepresentatives`,
and vanishing far energy at each root is
`LogCutoffSpatialBoundedness.vanishingFarEnergy_norm_of_logCutoff`. -/
theorem environmentAreaClockGeometry_of_logCutoff (e : Env)
    (hD : ∀ R : ℝ, 0 ≤ R → Spatial.maxDiamHittingBall (decode e) R < ∞)
    (hlog : ∀ (z : Vertex e.val → Plane) (o : Vertex e.val),
      ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ‖z o‖ ≤ r₀ ∧
        (∀ R : ℝ, r₀ ≤ R → ∀ v : Vertex e.val,
          Hits (decode e) (Metric.closedBall (0 : Plane) R) v →
          Metric.diam ((decode e).cell v : Set Plane) ≤ R / 100) ∧
        (∀ R : ℝ, r₀ ≤ R →
          LogCutoff.localMassENN (decode e)
              {v : Vertex e.val | Hits (decode e) (Metric.closedBall (0 : Plane) R) v}
            ≤ ENNReal.ofReal (C * R ^ 2))) :
    EnvironmentAreaClockGeometry e := by
  letI := nontrivial_vertex e
  obtain ⟨zrep, hzrep⟩ := exists_cellRepresentatives (decode e)
  refine ⟨zrep, hzrep, hD, fun o => ?_⟩
  obtain ⟨r₀, C, hr₀, hC, ho, hdiam, hW⟩ := hlog zrep o
  exact LogCutoffSpatialBoundedness.vanishingFarEnergy_norm_of_logCutoff (decode e)
    (decode_geometry e) zrep hzrep o hr₀ hC ho hdiam hW

/-! ## The almost-sure discharge -/

/-- **The geometric inputs hold almost surely under the main theorem's own hypotheses.** -/
theorem ae_environmentAreaClockGeometry (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ e ∂ν, EnvironmentAreaClockGeometry e := by
  filter_upwards [Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hmt hFE.ne,
    SpatialMaximalForFiniteEnergy.ae_exists_logCutoff_hypotheses ν hmt hFE.ne]
    with e hD hlog
  exact environmentAreaClockGeometry_of_logCutoff e hD.1 hlog

/-- **`EnvironmentAreaClockAdmissible` holds almost surely.**  The sole residual behind
`hdata`, discharged from mass transport and the finite (FE) moment. -/
theorem ae_environmentAreaClockAdmissible (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ e ∂ν, EnvironmentAreaClockAdmissible e :=
  (ae_environmentAreaClockGeometry ν hmt hFE).mono fun e he =>
    environmentAreaClockAdmissible_of_geometry e he

/-- **`hdata`, proved.**  The statement is the `hdata` clause of
`InvarianceAssembly.reflectedInvarianceConclusions_of_named_inputs`, copied verbatim, under the
main theorem's own hypotheses `[IsProbabilityMeasure ν]`, `MassTransport ν`,
`FiniteEnergyMoment ν`. -/
theorem ae_environmentWalkData (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG :=
  ae_environmentWalkData_of_ae_geometry ν (ae_environmentAreaClockGeometry ν hmt hFE)

end ReflectedGMS.AreaClockAdmissibleDischarge

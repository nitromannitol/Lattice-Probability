/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MesoModel.FinalAssembly at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MesoscopicControlWith
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Recurrent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTGraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCellCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.ConeRealization
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.FinalAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeCompare
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.WeightedMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.AreaScalingHolds
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.OuterMeasure.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.BadEventProposition
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.ProducersBadEventItinerary
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.ScaledGridControl
import LatticeProb.Bonanno.MatedCRTHarmonic.CellularFacts.Basic
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.MesoInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianLaw
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.LocalFiniteness
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Adj
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.Dart
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsConnectedSet
import LatticeProb.Bonanno.MatedCRTHarmonic.HarmonicInfinity.Mesoscopic
import LatticeProb.Bonanno.MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Harm
import LatticeProb.Bonanno.MatedCRTHarmonic.Harmonic.Graph
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.Chain
import LatticeProb.Bonanno.MatedCRTHarmonic.GoodScales.Bound
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.AnnularEvent
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VerticesMeeting
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTTwoSidedMin
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.CellArea
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Model
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.L27Bridge
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.MeshMeasurableWalk
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.GraphMeasurability
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.JointScalingOPath
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeScaling.FieldLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Main
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.OpenSupport
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.CurveLaws
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.OPositiveRadii
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointProof
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Theorem14
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.Annulus38

/-!
# Final cell-model assembly

The conditional cell-model theorem below has, as its only extra hypotheses, the stated probabilistic inputs:

| hypothesis | landed statement | producer |
|---|---|---|
| `hAnnulus38` | `MesoModel.Annulus38OneScaleBadBound M.coupled.family M.ρ` (per-scale [18] Lemma 3.8) | the one-scale estimate and Lemma 2.7 |
| `hREC` | `MesoModel.MatedCRTRecurrencePathScaleInput γ` | the recurrence and one-scale estimates |

Each hypothesis is quantified by `FinalForAllCouplings`: it is required only at
the realization (`MoTInput.unitMesoModelOfCoupling`, `MoTInput.coneRealizationOfCoupling`) of a mating-of-trees
coupling `D` of some `γ ∈ (0, 2)` on a standard Borel space, which is the weakest form the proof uses; a producer
proved for every model/realization closes it through `finalForAllCouplings_of_forall`.

The other inputs are supplied by the following results (`final_cellModelExists_of_coupling` is the per-coupling core):
* the waypoint input `CellFamily.WaypointStrongMarkovInputFixed2` (`waypointStrongMarkovInputFixed2_holds`);
* the cone's unit-disc area moments `CellScaling.AreaBallMoment` (`GMCFacts.areaBallMoment_holds`; [16] Lemma A.3);
* the cone's area scaling law `CellScaling.AreaScalingLaw` (`ConeScaling.areaScalingLaw_holds`; DMS
  Prop 4.13(i) and random-dilation coordinate change);
* Peanosphere/G0 (`MoTInput.ae_peanosphere`, `ae_sideStrict_allMeshes`);
* the area parametrization `CellScaling.AreaParametrization` from the v3 field `areaParam` stated for every vague limit
  and the SLE-free existence of the cone area limit (`GMCFacts.coneAreaExists_holds`), via
  `final_areaParametrization_of_reparam`;
* the boundary-length covariance from the bundle field `boundaryLength`;
* the corrected Lemma 2.7 bad-event input from the bundle's GHM15 Prop 3.4 field
  (`final_segmentsContainBalls_of_reparam`), `GMCFacts.gmcLowerTail_holds`, `GMCFacts.areaDominates_toCellModel`
  and `lemma27CellDiamBad_of_cone`;
* the corrected Lemma 3.8 bad-event input from `hAnnulus38` (`annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound`);
* `cellModelExists_of_cone` (the scaling, cell-count, annular, and mesoscopic-control estimates on the model),
  and `matedCRTRecurrenceInput_of_theorem14ScaleInput`.
No frozen theorem anchor is imported.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-! ### The quantifier of the remaining inputs -/

/-! ### Landed producers at one coupling -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}
/-- **Peanosphere/G0 at the coupling** (bundle fields `spaceFilling`, `areaParam`, `merge`, `onlyMerge`,
`boundaryLawBM`, through MTC's `MoTInput.ae_peanosphere`, `MoTInput.ae_sideStrict_allMeshes` and G0BM): the scaled-grid estimate Peanosphere input of the realization's mesh family. -/
theorem final_peanosphereG0_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    CellFamily.PeanosphereG0 (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family := by
  let M := MoTInput.unitMesoModelOfCoupling D hstd hγ
  have hpeano := MoTInput.ae_peanosphere D
  have hside := MoTInput.ae_sideStrict_allMeshes D
  have hbm := MoTInput.ae_bundleBM_eq D
  have hcurve := MoTInput.ae_bundleCurve_eq D
  intro k
  change ∀ᵐ ω ∂P, ∃ (path : MatedCRT.Path2) (curve : ℝ → ℂ)
    (h : MatedCRT.IsLocallyFinite (CellFamily.mesh k) path)
    (H : CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) path h) 0),
      RouteM.Peanosphere path curve ∧ RouteM.SideStrict (CellFamily.mesh k) path ∧
      (∀ x y, (M.coupled.family.G k ω).adj.Adj x y ↔
        (MatedCRT.graph (CellFamily.mesh k) path h).adj.Adj x y) ∧
      (∀ x, (M.coupled.family.H k ω).cell x = H.cell x) ∧
      ∀ x, H.cell x = curve '' Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)
  filter_upwards [hpeano, hside, hbm, hcurve] with ω hp hs hbmω hcurveω
  refine ⟨MoTInput.bundleBM D ω, MoTInput.bundleCurve D ω,
    (MoTInput.bundleGeometry D ω k).1, (MoTInput.bundleGeometry D ω k).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbmω, hcurveω]
    exact hp
  · rw [hbmω]
    exact hs k
  · intro x y
    rfl
  · intro x
    rfl
  · intro x
    exact congrArg (fun f : ℤ → Set ℂ => f x) (MoTInput.bundleGeometry_cell D ω k)

/-- **Area parametrization at the coupling** (the area-parametrization premise): the v3 field `areaParam` (every vague limit of the area
approximations of the γ-cone field gives the curve segments their length) with `spaceFilling`'s `ηL 0 = 0`, and the
SLE-free existence of the cone area limit (`final_areaParametrization_of_reparam`). -/
theorem final_areaParametrization_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    CellScaling.AreaParametrization (MoTInput.coneRealizationOfCoupling D hstd hγ) := by
  have hηL0 : ∀ᵐ ω ∂P, ηL ω 0 = 0 := by
    filter_upwards [D.spaceFilling] with ω hω
    exact hω.2.2.1
  exact final_areaParametrization_of_reparam (MoTInput.coneRealizationOfCoupling D hstd hγ) ηL η
    (MoTInput.ae_bundleCurve_eq D) hηL0 D.areaParam

/-- **GHM15 Prop 3.4 at the coupling**: the bundle field `segmentsContainBalls` for `ηL` gives Lemma 2.7's
`SegmentsContainBalls` for the realization's cell model, whose curve is a.s. `η = ηL ∘ φ` (`areaParam`). -/
theorem final_segmentsContainBalls_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (hpar : CellScaling.AreaParametrization (MoTInput.coneRealizationOfCoupling D hstd hγ)) :
    GMSLemma27.SegmentsContainBalls ((MoTInput.coneRealizationOfCoupling D hstd hγ).toCellModel hpar) := by
  refine final_segmentsContainBalls_of_reparam _ ηL ?_ D.segmentsContainBalls
  filter_upwards [D.areaParam, MoTInput.ae_bundleCurve_eq D] with ω hω hcω
  rcases hω with ⟨⟨φ, -, hφ⟩, -⟩
  have hc : MoTInput.bundleCurve D ω = η ω := hcω
  refine ⟨φ, fun t => ?_⟩
  change MoTInput.bundleCurve D ω t = ηL ω (φ t)
  rw [hc]
  exact hφ t

end Coupling

/-! ### The two v3 theorems, conditional on the remaining inputs -/

end MatedCRTHarmonic.MesoModel

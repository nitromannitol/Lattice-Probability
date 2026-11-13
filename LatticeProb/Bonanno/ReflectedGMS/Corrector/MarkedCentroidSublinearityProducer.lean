/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedCentroidSublinearityProducer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CentroidSublinearityFromResidual
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly

/-!
# `MarkedCentroidSublinearity` from small residuals

`HarmonicCoordinateAssembly.harmonicCoordinateConclusions_of_named_inputs` carries ten open
inputs.  Tonight's adversarial statement audit showed that the zero field satisfies
`GradientCovariant`, `NormalizedCovariant`, `RootNormalized`, `DiscreteHarmonicity` and
`FullRectangleOrthogonality`, so the sublinearity clause is the sole carrier of
non-degeneracy in the harmonic main theorem, and the assembly derives the
representative-independent half of that clause from its centroid half `hsub`.  This module
**discharges `hsub`**: it produces
`HarmonicCoordinateAssembly.MarkedCentroidSublinearity ν ms` from

* `hharm` — `MarkedHarmonicity ν ms`, an input the assembly already takes, whose
  `FullRectangleMinimizer` half is precisely the variational minimality that the maximum
  principle of `Corrector/GoodGridMaximumPrinciple` consumes;
* `MarkedSmallBlockResidual ν ms` — `s:eq:smallresidual` in maximal-function form, the
  genuinely open residue (see `Corrector/CentroidSublinearityFromResidual`);
* `MarkedGeometricMassQuadratic ν` — `s:eq:Wbound` in the quadratic form `W(R) ≤ K R²`,
  which is *not* the (already discharged) finite-radius form
  `PatchCentroidTraceFiniteEnergy.SpatialDiameterCellBounds`;
* the manuscript's own `s:eq:MTP` and finite (FE) moment, through the checked producers
  `Spatial.ae_maxDiamHittingBall_finite_and_sublinear` (`s:eq:DR`) and
  `Spatial.ae_notMem_boundaryMask_of_massTransport` (the root exists almost surely).

Nothing about the covariance, measurability or convergence inputs is touched, and
`HarmonicCoordinateAssembly` is not modified.

The final statements re-express the assembly's reduction with `hsub` replaced by the two
inputs above; they are implications, and they do not prove the harmonic-coordinate theorem.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace ReflectedGMS.MarkedCentroidSublinearityProducer

open Code StatementIngredients EnvironmentFields EnvironmentLaws RootDensities
open HarmonicLawIngredients DyadicApproximation HarmonicMainStatement
open MarkedLimitingCoordinateMeasurability UnmarkedCoordinateDescent
open NonmacroscopicSelectedBlocks Spatial PatchCentroidTraceFiniteEnergy
open HarmonicCoordinateAssembly CentroidSublinearityFromResidual

/-- **OPEN INPUT (`s:eq:Wbound`, quadratic form).**  Almost every environment carries a
single constant `K` with `W(R) = ∑_{H ∈ 𝓗(clB R)} d_H² π*(H) ≤ K R²` for all large `R`.

This is *stronger* than the finite-radius half `SpatialDiameterCellBounds` discharged by
`Spatial/SpatialMaximalForFiniteEnergy.ae_spatialDiameterCellBounds`, which only asserts
`W(R) < ∞` at each radius.  Its intended producer is the same spatial maximal bound
`Spatial.ae_exists_ballBound_rootedFiniteEnergyDensity` together with the identity
`a_H ρ_FE(H) = d_H²(π_H + π*_H)` of
`Spatial/AlmostSureSpatialDiameterBounds.volume_mul_finiteEnergyDensity_eq`; the only
missing step is the comparison of the `ℝ≥0∞`-valued `reciprocalConductanceMass` with the
real `piStar`, which no module in the project currently provides. -/
def MarkedGeometricMassQuadratic (ν : Measure Env) : Prop :=
  ∀ᵐ e : Env ∂ν, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ R : ℝ in atTop,
    patchDiameterReciprocalConductanceMass (decode e)
        (hittingVertices (decode e) (Metric.closedBall (0 : Plane) R))
      ≤ ENNReal.ofReal (K * R ^ 2)

/-- **OPEN INPUT (`s:eq:smallresidual`, marked level).**  Almost surely the marked limit is
approximable by the manuscript's block interpolants in the maximal-function sense: for every
`ε > 0` some nonzero stage carries an actual block interpolant whose residual against the
limit has ball-maximal specific energy below `ε`. -/
def MarkedSmallBlockResidual (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw,
    SmallBlockResidual (decode ω.1) ω.2 (markedPotential ms ω)

/-- **`hsub` discharged.**  The centroid half of `s:eq:sublinear` for the marked limit,
from full-rectangle minimality (`hharm`), the small-residual input, the quadratic geometric
mass bound, and the manuscript's own environment hypotheses. -/
theorem markedCentroidSublinearity_of_smallBlockResidual (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν)
    (hFE : (∫⁻ e : Env, rootedFiniteEnergyDensity (decode e) 0 ∂ν) ≠ ∞)
    (ms : ℕ → ℕ) (hharm : MarkedHarmonicity ν ms)
    (hmass : MarkedGeometricMassQuadratic ν) (hres : MarkedSmallBlockResidual ν ms) :
    MarkedCentroidSublinearity ν ms := by
  have hgeom := Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hν hFE
  have hmask := Spatial.ae_notMem_boundaryMask_of_massTransport ν hν
  filter_upwards [hharm, hres, ae_marked_of_ae_env ν hgeom, ae_marked_of_ae_env ν hmask,
    ae_marked_of_ae_env ν hmass] with ω hh hr hg hm hKe
  obtain ⟨K, hK0, hW⟩ := hKe
  obtain ⟨vr, hvr, hint⟩ :=
    rootAt_eq_some_of_not_mem_boundaryMask (decode ω.1) (decode_geometry ω.1) hm
  have hvr0 : (0 : Plane) ∈ ((decode ω.1).cell vr : Set Plane) := interior_subset hint
  have hΦr : markedPotential ms ω vr = 0 := by
    show markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) vr.val) = 0
    rw [baseLabel_eq_of_rootAt hvr]
    exact (isDifferenceField_markedDifferenceField ms ω).1 vr
  exact uniformlySublinearCorrector_of_smallBlockResidual (decode ω.1) (decode_geometry ω.1)
    (decode_aeLineConnected ω.1) ω.2 hg.2.1 hh.2.1 hK0 hW hr hvr0 hΦr

/-! ### The reduction with `hsub` discharged -/

end ReflectedGMS.MarkedCentroidSublinearityProducer

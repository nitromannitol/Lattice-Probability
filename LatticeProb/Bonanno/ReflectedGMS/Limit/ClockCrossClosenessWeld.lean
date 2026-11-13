/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.ClockCrossClosenessWeld at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainTheoremTwoAtoms
import LatticeProb.Bonanno.ReflectedGMS.Limit.ClockCrossCloseness

/-!
# `hcross` from the exact holding mesh (and `hlln`): main theorem 2 at `hlln` + (P3)

`InvarianceMainTheoremTwoAtoms.reflectedInvarianceConclusions_validLaw_of_two_atoms` takes two
named inputs, `hlln : UniformDirectionalBracketLLN ν` and `hcross : UniformClockCrossCloseness ν`.
`ClockCrossClosenessProducer.clockCrossClosenessSlot_of_mesh` produces the cross-closeness slot
from the exponential-clock modulus `hmodExp` and the exact holding mesh (P3)
`ClockMeshInputSample.ExactHoldingMesh`.  This file welds the two.

## Where `hmodExp` comes from, and why `hlln` is used here

`hmodExp` is `CompactContainmentProducer.hmodExp_of_clock_inputs_and_arrays`, from `hsub`,
`hdiam` and the martingale arrays `harray`.  `hsub`/`hdiam` are almost sure consequences of
`MassTransport ν`, (FE) and the harmonic coordinate (exactly as in
`ClockCrossClosenessProducer.aeAnalyticPacket_of_meshPacket`).  `harray` is
`ActualThresholdArray.harray_of_canonicalBracket`, which needs the walk's `CanonicalBracket`
(discharged: `hbracket_of_ae_diagonalCompensatedSquares` with bracket atom 2
`InvarianceMainTheoremTwoAtoms.uniformDiagonalCompensatedSquares`) **and the diagonal bracket
LLN**, which is `hlln` read at the coordinate directions.  So the cross-closeness is produced from
`hlln` together with the mesh; since main theorem 2 already takes `hlln`, this costs nothing new.

## Results

* `AeExactHoldingMesh`, `UniformExactHoldingMesh` — (P3) at every start, gated exactly as the
  atom `AeClockCrossCloseness` (almost every environment, walk data, pathwise clock clauses);
* `aeClockCrossCloseness_of_mesh`, `uniformClockCrossCloseness_of_mesh` — `hcross` from `hmt`,
  (FE), `hlln` and the mesh;
* `reflectedInvarianceConclusions_of_lln_and_mesh` and its `validLaw` form — main theorem 2
  from `hlln` and the mesh.

**CONDITIONAL** on `hlln` and the mesh; certifies neither, nor either main theorem.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.ClockCrossClosenessWeld

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open InvarianceMainStatement QuenchedFormulation ReflectedWalk
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.AnalyticPacketAssembly
open ReflectedGMS.ClockMeshInputSample
open ReflectedGMS.GaussianLimitIdentification

/-- **The exact holding mesh (P3) at every start**, gated exactly as the cross-closeness atom
`AeClockCrossCloseness`: almost every environment, every exhaustion carrying the walk data,
every start, every choice of lifts satisfying the pathwise clock clauses. -/
def AeExactHoldingMesh (ν : Measure Env) (Φ : CellField) : Prop :=
  ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
    letI := hnt
    ∀ (D : (decode e).graph.Exhaustion)
      (hG : (decode e).graph.toSimpleGraph.Connected),
      EnvironmentWalkData e D hG →
      ∀ (start : Vertex e.val)
        (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
        (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
        PathwiseClockClauses e D hG Φ start Xexp Xexact M →
        ExactHoldingMesh (decode e) D hG start

/-- The exact holding mesh, uniformly in the harmonic coordinate (the gate only). -/
def UniformExactHoldingMesh (ν : Measure Env) : Prop :=
  ∀ Φ : CellField, IsHarmonicCoordinate ν Φ → AeExactHoldingMesh ν Φ

/-- **`AeClockCrossCloseness` from the directional bracket LLN and the mesh.**  CONDITIONAL on
`hlln`, `hmesh`. -/
theorem aeClockCrossCloseness_of_mesh (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ)
    (hlln : AeDirectionalBracketLLN ν Φ) (hmesh : AeExactHoldingMesh ν Φ) :
    AeClockCrossCloseness ν Φ := by
  filter_upwards [ae_all_iff.2
      (CoordinateLocallySquareIntegrableWeld.hbracket_of_ae_diagonalCompensatedSquares ν hmt
        hFE Φ hΦ (InvarianceMainTheoremTwoAtoms.uniformDiagonalCompensatedSquares ν hmt hFE Φ hΦ)),
    hlln, hmesh, ae_submacroscopicDiameters ν hmt hFE,
    Spatial.ae_maxDiamHittingBall_finite_and_sublinear ν hmt hFE.ne, hΦ.2.2.2.2.1]
    with e hbre hllne hme hdiam hdec hcorr
  intro hnt D hG hdat start Xexp Xexact M hclock z hz
  have : Nontrivial (Vertex e.val) := hnt
  have hbr : CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG start) M :=
    hbre start.1 start.2 hnt D hG hdat Xexp Xexact M hclock
  have hsub : UniformlySublinearError (decode e) (Φ.at e) (z.at e) :=
    HarmonicCoordinateAssembly.uniformlySublinearError_of_representatives (decode e)
      (decode_geometry e) hdec.2.1 hcorr.2.2.2.2.1 (fun v => hz e v)
  have harray := ActualThresholdArray.harray_of_canonicalBracket e D hG Φ start Xexp Xexact M
    hclock hbr
    (fun k => bilinForm (meanCovariance ν Φ) (EuclideanSpace.single k 1)
      (EuclideanSpace.single k 1))
    (fun k => by
      have h := hllne hnt D hG hdat start M hbr (EuclideanSpace.single k 1)
      rwa [ActualThresholdArray.dirBracket_single] at h)
  exact ClockCrossClosenessProducer.clockCrossClosenessSlot_of_mesh e D hG hdat z Φ start Xexp
    Xexact M hclock
    (CompactContainmentProducer.hmodExp_of_clock_inputs_and_arrays e D hG z Φ start Xexp Xexact
      M hdat hclock hz hsub hdiam harray)
    (hme hnt D hG hdat start Xexp Xexact M hclock)

/-- **`hcross` from `hlln` and the mesh.**  CONDITIONAL on both. -/
theorem uniformClockCrossCloseness_of_mesh (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hlln : UniformDirectionalBracketLLN ν) (hmesh : UniformExactHoldingMesh ν) :
    UniformClockCrossCloseness ν :=
  fun Φ hΦ => aeClockCrossCloseness_of_mesh ν hmt hFE Φ hΦ (hlln Φ hΦ) (hmesh Φ hΦ)

/-- **The same at the main theorem's own law.** -/
theorem reflectedInvarianceConclusions_validLaw_of_lln_and_mesh
    (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValid P)
    (hmt : AmbientMassTransport P hP) (hFE : FiniteEnergyMoment (validLaw P hP))
    (hlln : UniformDirectionalBracketLLN (validLaw P hP))
    (hmesh : UniformExactHoldingMesh (validLaw P hP)) :
    ReflectedInvarianceConclusions (validLaw P hP) :=
  InvarianceMainTheoremTwoAtoms.reflectedInvarianceConclusions_validLaw_of_two_atoms P hP hmt
    hFE hlln (uniformClockCrossCloseness_of_mesh (validLaw P hP) hmt hFE hlln hmesh)

end ReflectedGMS.ClockCrossClosenessWeld

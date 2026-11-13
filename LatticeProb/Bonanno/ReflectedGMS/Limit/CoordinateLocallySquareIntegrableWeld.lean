/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CoordinateLocallySquareIntegrableWeld at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.CoordinateLocallySquareIntegrable
import LatticeProb.Bonanno.ReflectedGMS.Limit.CanonicalOccupationDischarge

/-!
# Weld: the `hbracket` input from bracket atom 2 alone

`BracketClausesScalarReduction.hbracket_of_ae_scalar_inputs` consumes, almost surely in the
environment, the three per-start inputs `CanonicalOccupationLocallyFinite`,
`CoordinateLocallySquareIntegrable` (bracket atom 1) and `DiagonalCompensatedSquares` (bracket
atom 2).  The first is `CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite` and the
second is now `CoordinateLocallySquareIntegrableProof.ae_coordinateLocallySquareIntegrable`, both
from `MassTransport ν`, the (FE) moment and `IsHarmonicCoordinate ν Φ`.  The elaboration of
`hbracket_of_ae_diagonalCompensatedSquares` below is the machine check that atom 1 fits its
consumer verbatim.

**This is an honestly conditional result**: `hsq` (bracket atom 2) is open.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace ReflectedGMS.CoordinateLocallySquareIntegrableWeld

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open InvarianceMainStatement QuenchedFormulation ReflectedWalk
open ReflectedGMS.InvarianceAssembly
open ReflectedGMS.BracketClausesScalarReduction

/-- **`hbracket` from bracket atom 2 alone** (conditional on `hsq`).  The conclusion is verbatim
that of `BracketClausesScalarReduction.hbracket_of_ae_scalar_inputs`. -/
theorem hbracket_of_ae_diagonalCompensatedSquares (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hΦ : IsHarmonicCoordinate ν Φ)
    (hsq : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG →
        ∀ (start : Vertex e.val)
          (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
          (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
          PathwiseClockClauses e D hG Φ start Xexp Xexact M →
          DiagonalCompensatedSquares e D hG Φ start M) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG ⟨n, hn⟩) M := by
  refine hbracket_of_ae_scalar_inputs ν Φ ?_
  filter_upwards [CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite ν hmt hFE Φ hΦ,
    CoordinateLocallySquareIntegrableProof.ae_coordinateLocallySquareIntegrable ν hmt hFE Φ hΦ,
    hsq] with e hocc hcoord hsqe
  intro hnt D hG hdat start Xexp Xexact M hpcc
  exact ⟨hocc hnt D hG hdat start, hcoord hnt D hG hdat start Xexp Xexact M hpcc,
    hsqe hnt D hG hdat start Xexp Xexact M hpcc⟩

end ReflectedGMS.CoordinateLocallySquareIntegrableWeld

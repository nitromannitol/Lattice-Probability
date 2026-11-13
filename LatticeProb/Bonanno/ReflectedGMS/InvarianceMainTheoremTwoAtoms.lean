/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.InvarianceMainTheoremTwoAtoms at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainTheoremThreeAtoms
import LatticeProb.Bonanno.ReflectedGMS.Limit.DiagonalCompensatedSquaresProducer

/-!
# Main theorem 2 from exactly two process-lane atoms

`InvarianceMainTheoremThreeAtoms.reflectedInvarianceConclusions_of_three_atoms` needed bracket
atom 2 on the area clock, `hsq : UniformDiagonalCompensatedSquares ν`.
`Limit/DiagonalCompensatedSquaresProducer.ae_diagonalCompensatedSquares` proves its body at every
harmonic coordinate from `MassTransport ν` and (FE) alone, so `hsq` is discharged here.

## The two remaining named inputs

* `hlln : UniformDirectionalBracketLLN ν` — the directional bracket LLN at every start;
* `hcross : UniformClockCrossCloseness ν` — `p:eq:clockequiv`.

**This file proves no main theorem**: it is an implication whose two named inputs are open.
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.InvarianceMainTheoremTwoAtoms

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients
open InvarianceMainStatement
open ReflectedGMS.AnalyticPacketAssembly

/-- **Bracket atom 2, discharged**: `UniformDiagonalCompensatedSquares ν` from the main theorem's
own hypotheses. -/
theorem uniformDiagonalCompensatedSquares (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) :
    UniformDiagonalCompensatedSquares ν :=
  fun Φ hΦ => DiagonalCompensatedSquaresProof.ae_diagonalCompensatedSquares ν hmt hFE Φ hΦ

/-- **`ReflectedInvarianceConclusions ν` from `hlln` and `hcross` alone.**  An implication that
certifies neither input. -/
theorem reflectedInvarianceConclusions_of_two_atoms
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hlln : UniformDirectionalBracketLLN ν)
    (hcross : UniformClockCrossCloseness ν) :
    ReflectedInvarianceConclusions ν :=
  InvarianceMainTheoremThreeAtoms.reflectedInvarianceConclusions_of_three_atoms ν hmt hFE
    (uniformDiagonalCompensatedSquares ν hmt hFE) hlln hcross

/-- **The same at the main theorem's own law.**  Still an implication with two open inputs. -/
theorem reflectedInvarianceConclusions_validLaw_of_two_atoms
    (P : Measure RawCode) [IsProbabilityMeasure P] (hP : SupportedOnValid P)
    (hmt : AmbientMassTransport P hP) (hFE : FiniteEnergyMoment (validLaw P hP))
    (hlln : UniformDirectionalBracketLLN (validLaw P hP))
    (hcross : UniformClockCrossCloseness (validLaw P hP)) :
    ReflectedInvarianceConclusions (validLaw P hP) :=
  reflectedInvarianceConclusions_of_two_atoms (validLaw P hP) hmt hFE hlln hcross

end ReflectedGMS.InvarianceMainTheoremTwoAtoms

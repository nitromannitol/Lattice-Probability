/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.StageBlockEnergyHarmonicWeld at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageBlockEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.CopyDifferenceOrthogonalityLimit

/-!
# The harmonic-coordinate conclusions from `s:eq:MTP` and (FE) alone

`Corrector/CopyDifferenceOrthogonalityLimit.harmonicCoordinateConclusions_of_projection` reduces
`HarmonicCoordinateConclusions ν` to the single input `hproj`
(`SpecificEnergyConvergence.MarkedNestedProjectionBound ν`), and
`Corrector/StageBlockEnergy.markedNestedProjectionBound` proves `hproj` from `MassTransport ν`
and `FiniteEnergyMoment ν`.  This module is the one-line composition, on an arbitrary
probability environment law and at the main theorem's own law `validLaw P hP`.

Both statements are pure applications: no binder is restated and none is inlined.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ReflectedGMS.StageBlockEnergyHarmonicWeld

open Code EnvironmentLaws HarmonicLawIngredients HarmonicMainStatement
open HarmonicCoordinateAssembly

/-- **The harmonic-coordinate conclusions**, from the manuscript's `s:eq:MTP` and the (FE)
moment alone. -/
theorem harmonicCoordinateConclusions (ν : Measure Env) [IsProbabilityMeasure ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) : HarmonicCoordinateConclusions ν :=
  CopyDifferenceOrthogonalityLimit.harmonicCoordinateConclusions_of_projection ν hν hFE
    (StageBlockEnergy.markedNestedProjectionBound ν hν hFE)

/-- **The same at the main theorem's own law `validLaw P hP`.** -/
theorem harmonicCoordinateConclusions_validLaw (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValid P) (hmt : AmbientMassTransport P hP)
    (hFE : FiniteEnergyMoment (validLaw P hP)) :
    HarmonicCoordinateConclusions (validLaw P hP) :=
  CopyDifferenceOrthogonalityLimit.harmonicCoordinateConclusions_validLaw_of_projection P hP hmt
    hFE (StageBlockEnergy.markedNestedProjectionBound (validLaw P hP) hmt hFE)

end ReflectedGMS.StageBlockEnergyHarmonicWeld

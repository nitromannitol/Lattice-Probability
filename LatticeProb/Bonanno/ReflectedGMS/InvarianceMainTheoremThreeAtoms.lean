/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.InvarianceMainTheoremThreeAtoms at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.AnalyticPacketAssembly
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageBlockEnergyHarmonicWeld

/-!
# Main theorem 2 from exactly three process-lane atoms

`Limit/AnalyticPacketAssembly.reflectedInvarianceConclusions_of_frontier_atoms` still carried the
harmonic-side binders `hproj` and `hzero`, the latter quantified over **every** strictly monotone
`ms`.  `hproj` is proved, but `hzero` at an arbitrary `ms` is not what
`Corrector/CopyDifferenceOrthogonalityLimit.originEnergy_eq_zero` gives (it needs `hconv`/`hpatch`
at that `ms`).  Both binders were only ever used to produce a harmonic coordinate, through
`HarmonicCoordinateTwoInputs.harmonicCoordinateConclusions_of_two_inputs`.

Main theorem 1 is proved (`MainTheorems.harmonicCoordinateMainTheorem`), and its
`ν`-level form `StageBlockEnergyHarmonicWeld.harmonicCoordinateConclusions` supplies the coordinate
from `MassTransport ν` and (FE) alone.  Every atom below is uniform in the coordinate
(`∀ Φ, IsHarmonicCoordinate ν Φ → …`), so the coordinate it supplies is the one they are read at.
This file is `ScalarBracketMainTheoremsWeld.reflectedInvarianceConclusions_of_harmonic_inputs_and_scalar_atoms`
with that one elimination replaced, and `hscalar`, `hlimit` supplied by the analytic packet.

## The three remaining named inputs

* `hsq : UniformDiagonalCompensatedSquares ν` — bracket atom 2 on the area clock;
* `hlln : UniformDirectionalBracketLLN ν` — the directional bracket LLN at every start;
* `hcross : UniformClockCrossCloseness ν` — `p:eq:clockequiv`.

**This file proves no main theorem**: it is an implication whose three named inputs are open.
`AmbientEnvironmentErgodic` is not a hypothesis because no step uses it (it enters, if at all,
through `hlln`).
-/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.InvarianceMainTheoremThreeAtoms

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients
open InvarianceMainStatement
open ReflectedGMS.LocalBracketMainTheoremsWeld ReflectedGMS.ScalarBracketMainTheoremsWeld
open ReflectedGMS.HlimitAssemblyAtoms ReflectedGMS.BracketClausesScalarReduction
open ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.AnalyticPacketAssembly

/-- **`ReflectedInvarianceConclusions ν` from `hsq`, `hlln`, `hcross` alone.**  The harmonic
coordinate is main theorem 1's; `hscalar` and `hlimit` come from the analytic packet.  An
implication that certifies none of its three inputs. -/
theorem reflectedInvarianceConclusions_of_three_atoms
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (hsq : UniformDiagonalCompensatedSquares ν)
    (hlln : UniformDirectionalBracketLLN ν)
    (hcross : UniformClockCrossCloseness ν) :
    ReflectedInvarianceConclusions ν := by
  obtain ⟨Φ, hΦ⟩ := StageBlockEnergyHarmonicWeld.harmonicCoordinateConclusions ν hmt hFE
  have hscalar := uniformScalarBracketClauses_of_diagonalCompensatedSquares ν hmt hFE hsq
  have hlimit := uniformAreaClockLimit_of_atoms ν hmt hFE hsq hlln hcross
  have hcut := SpatialCutoffEnvironment.ae_hasSpatialCutoffs_of_isHarmonicCoordinate
    ν hmt hFE Φ hΦ
  refine BracketClausesScalarReduction.reflectedInvarianceConclusions_of_scalar_bracket_inputs
    ν hmt hFE Φ hΦ
    (ae_hreg_of_cutoffs_and_continuity ν hmt hFE Φ hcut
      (NonvertexContinuityEnvironment.ae_hcont_of_cutoffs ν hmt hFE Φ hcut))
    ?_ (hlimit Φ hΦ)
  filter_upwards
    [CanonicalOccupationDischarge.ae_canonicalOccupationLocallyFinite ν hmt hFE Φ hΦ,
      hscalar Φ hΦ] with e hocc hsc
  intro hnt D hG hdat start Xexp Xexact M hpcc
  have : Nontrivial (Vertex e.val) := hnt
  obtain ⟨hmart, hsq'⟩ := hsc hnt D hG hdat start Xexp Xexact M hpcc
  exact ⟨hocc hnt D hG hdat start, hmart, hsq'⟩

end ReflectedGMS.InvarianceMainTheoremThreeAtoms

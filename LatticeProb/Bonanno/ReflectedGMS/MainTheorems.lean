/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.MainTheorems at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.StageBlockEnergyHarmonicWeld
import LatticeProb.Bonanno.ReflectedGMS.InvarianceMainTheoremProof
import Mathlib.Util.AssertNoSorry

/-!
# Both main theorems of the AE-LC reflected-GMS manuscript

The two targets were stated on 2026-09-14 as propositions and have not been edited since:

* `HarmonicMainStatement.HarmonicCoordinateMainTheorem` — the ambient-law harmonic coordinate;
* `InvarianceMainStatement.ReflectedInvarianceMainTheorem` — the reflected invariance principle
  (validity, full trace-measurable mass transport, (FE) and environment-only ergodicity imply
  the conclusions (a)–(e)).

This file proves both, with no hypotheses:

* main theorem 1 is the universally quantified form of
  `StageBlockEnergyHarmonicWeld.harmonicCoordinateConclusions_validLaw` (the harmonic-coordinate
  conclusions at `validLaw P hP` from the manuscript's own `s:eq:MTP` and the (FE) moment; the
  chain behind it: `hproj` from `StageBlockEnergy.markedNestedProjectionBound`, the cross
  orthogonality `hzero` from `CopyDifferenceOrthogonalityLimit.originEnergy_eq_zero`, the
  measurable selection `hmeas` from `BlockInterpolantSelectionCandidate.measurable_gatedApproximant`);
* main theorem 2 is `InvarianceMainTheoremProof.reflectedInvarianceMainTheorem`.

The proof map from manuscript labels to Lean declarations is `outputs/manuscript-lean-index.md`.
-/

set_option autoImplicit false

namespace ReflectedGMS.MainTheorems

/-- **Main theorem 1** (harmonic coordinate).  No named input remains: the hypotheses are the
manuscript's own mass transport and finite-energy moment. -/
theorem harmonicCoordinateMainTheorem : HarmonicMainStatement.HarmonicCoordinateMainTheorem :=
  fun P _ hP hmt hFE =>
    StageBlockEnergyHarmonicWeld.harmonicCoordinateConclusions_validLaw P hP hmt hFE

/-- **Main theorem 2** (reflected invariance principle). -/
theorem reflectedInvarianceMainTheorem : InvarianceMainStatement.ReflectedInvarianceMainTheorem :=
  InvarianceMainTheoremProof.reflectedInvarianceMainTheorem

end ReflectedGMS.MainTheorems

assert_no_sorry ReflectedGMS.MainTheorems.harmonicCoordinateMainTheorem
assert_no_sorry ReflectedGMS.MainTheorems.reflectedInvarianceMainTheorem

#print axioms ReflectedGMS.MainTheorems.harmonicCoordinateMainTheorem
#print axioms ReflectedGMS.MainTheorems.reflectedInvarianceMainTheorem

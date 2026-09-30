import LatticeProb.External.FeyMeesterRedigLeastAction

/-!
# The least action principle of Fey, Meester and Redig, proved

The proposition `LatticeProb.External.FeyMeesterRedigLeastAction` holds, by
`LatticeProb.Sandpile.le_of_isLegalToppling_of_eventually_eq`; neither `1 ≤ d` nor the
nonnegativity of `s0` is needed. A formalization that carries the proposition as a hypothesis
can discharge it with `feyMeesterRedigLeastAction_holds`.
-/

namespace LatticeProb.External

open LatticeProb.Sandpile

/-- **The least action principle of Fey, Meester and Redig holds**: a legal toppling procedure
never exceeds the final odometer of a stabilizing legal procedure. -/
theorem feyMeesterRedigLeastAction_holds : FeyMeesterRedigLeastAction :=
  fun _ _ _ _ _ _ hu hv _ hvw hw k x => le_of_isLegalToppling_of_eventually_eq hu hv hvw hw k x

end LatticeProb.External

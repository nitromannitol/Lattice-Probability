import LatticeProb.Sandpile.FLP.Shell
import LatticeProb.Sandpile.FLP.Radius

/-!
# The radius bound of Fey, Levine and Peres, proved

The proposition `LatticeProb.External.FeyLevinePeresRadius` (Theorem 1.1 of A. Fey, L. Levine
and Y. Peres, *Growth rates and explosions in sandpiles*, J. Stat. Phys. 138 (2010), 143–159)
holds: `LatticeProb.Sandpile.FLP.feyLevinePeresRadius_of_shell` derives it from the shell bound
of Levine and Peres, which `LatticeProb.Sandpile.FLP.levinePeresShellBound` proves. A
formalization that carries the proposition as a hypothesis can discharge it with
`feyLevinePeresRadius_holds`.
-/

namespace LatticeProb.External

/-- **The radius bound of Fey, Levine and Peres holds**: for `d ≤ h ≤ 2d - 2` and every
`ε > 0`, the sites that topple from `h + n δ₀` eventually lie in the cube of radius
`((d + ε) / (2d - 1 - h)) (n / ω_d)^{1/d}`. -/
theorem feyLevinePeresRadius_holds : FeyLevinePeresRadius :=
  LatticeProb.Sandpile.FLP.feyLevinePeresRadius_of_shell
    LatticeProb.Sandpile.FLP.levinePeresShellBound

end LatticeProb.External

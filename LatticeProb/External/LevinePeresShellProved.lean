import LatticeProb.Sandpile.FLP.Shell

/-!
# The shell bound of Levine and Peres, proved

The proposition `LatticeProb.External.LevinePeresShellBound` holds, by
`LatticeProb.Sandpile.FLP.levinePeresShellBound`, the outer estimate in the proof of Theorem 4.1
of L. Levine and Y. Peres, *Strong spherical asymptotics for rotor-router aggregation and the
divisible sandpile*, Potential Anal. 30 (2009), 1–27. A formalization that carries the
proposition as a hypothesis can discharge it with `levinePeresShellBound_holds`.
-/

namespace LatticeProb.External

/-- **The shell bound of Levine and Peres holds**: for the background height `d - 1`, the
parallel odometer of `(d - 1) + n δ₀` is bounded on the shell `c'₁ r - 1 < |x| ≤ c'₁ r`,
uniformly in `n` and in time. -/
theorem levinePeresShellBound_holds : LevinePeresShellBound :=
  LatticeProb.Sandpile.FLP.levinePeresShellBound

end LatticeProb.External

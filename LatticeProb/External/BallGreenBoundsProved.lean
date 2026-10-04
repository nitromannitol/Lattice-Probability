import LatticeProb.External.BallGreenBounds

/-!
# The ball-killed Green estimates, proved

The proposition `LatticeProb.External.BallGreenBounds` holds, by
`LatticeProb.BallGreen.ballGreenBounds`. A formalization that carries the proposition as a
hypothesis can discharge it with `ballGreenBounds_holds`.
-/

namespace LatticeProb.External

/-- **The ball-killed Green estimates in dimension four hold.** -/
theorem ballGreenBounds_holds : BallGreenBounds := LatticeProb.BallGreen.ballGreenBounds

end LatticeProb.External

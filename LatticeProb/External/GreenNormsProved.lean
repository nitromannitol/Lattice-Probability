import LatticeProb.External.GreenNorms

/-!
# The two norms of the truncated Green function, proved

The proposition `LatticeProb.External.GreenNorms` holds, by `LatticeProb.greenNorms`. A
formalization that carries the proposition as a hypothesis can discharge it with
`greenNorms_holds`.
-/

namespace LatticeProb.External

/-- **The two norms of the truncated Green function have the stated orders** in every dimension. -/
theorem greenNorms_holds : GreenNorms := fun _ hd => greenNorms hd

end LatticeProb.External

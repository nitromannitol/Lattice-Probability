import Mathlib
import LatticeProb.Prob.ReturnTime

/-!
# The return-time Birkhoff sum, the induced family, and the linear-bound sets

Three definitions shared by every stage of the linear-bound Kingman theorem
(`LatticeProb.Prob.KingmanLinear`): `retSum T A j x`, the Birkhoff sum of the return time
`retTime T A` along the first-return map (the `j`-th return time); `indG g T A j x`, the family
`g` sampled along that Birkhoff sum (the induced family); and `linSet g C k`, the set of points
on which `g` obeys the linear bound `g n x ≤ C * n + k`.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `j`-th return time `R j = ∑_{i<j} r (S^i x)`. -/
noncomputable def retSum (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) : ℕ :=
  birkhoffSum (inducedMap T A) (retTime T A) j x

/-- The induced family `G j x = g (R j x) x`. -/
noncomputable def indG (g : ℕ → Ω → ℝ) (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) : ℝ :=
  g (retSum T A j x) x

/-- The sets on which the linear bound holds with constant `k`. -/
def linSet (g : ℕ → Ω → ℝ) (C : ℝ) (k : ℕ) : Set Ω := {x | ∀ n : ℕ, g n x ≤ C * n + k}

end LatticeProb

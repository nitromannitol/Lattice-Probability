/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTIsEdge at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTSideCond

/-!
# Frozen definition: `MatedCRT.IsEdge`

Consecutive vertices carry exactly one hard-wired edge (characterization `sideCond_succ`); a non-consecutive pair
carries an `L`-edge iff (1.1) holds for `L`, an `R`-edge iff it holds for `R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- The edges of the ε-mated-CRT map of the path `ω` ([18] (1.1)), as labelled triples
`(x, y, side)` with `x < y` (`side = false` is the `L`-edge, `true` the `R`-edge): consecutive vertices carry exactly
one edge (`(x, x + 1, false)`; (1.1) always holds for them, `sideCond_succ`); a non-consecutive pair carries its
`L`-edge iff (1.1) holds for `L` and its `R`-edge iff (1.1) holds for `R` (two parallel edges when both hold). -/
def IsEdge (ε : ℝ) (ω : Path2) (e : ℤ × ℤ × Bool) : Prop :=
  e.1 < e.2.1 ∧
    ((e.2.1 = e.1 + 1 ∧ e.2.2 = false) ∨
      (e.2.1 ≠ e.1 + 1 ∧ SideCond ε (fun t => if e.2.2 then (ω t).2 else (ω t).1) e.1 e.2.1))

end MatedCRT

end MatedCRTHarmonic

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.Recurrent at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HitTime
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.VertexPath

/-!
# Frozen definition: `LFMultigraph.Recurrent`

Hitting form: from every vertex the walk visits every vertex a.s. This is the
recurrence notion used throughout the library.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **Recurrence** of simple random walk, hitting form (`rfl`-equal to `HarmonicInfinity.Recurrent`): from every vertex `x` the walk visits every vertex `y` almost surely (: "the simple random
walk on `G^ε` is recurrent"; on a connected graph this is equivalent to a.s. return). -/
def Recurrent : Prop :=
  ∀ x y : V, G.walkLaw x {ω | Markov.hitTime ({y} : Set V) (G.vertexPath ω) ≠ ⊤} = 1

end LFMultigraph

end MatedCRTHarmonic

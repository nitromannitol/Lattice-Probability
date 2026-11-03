/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.WalkLaw at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernel
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernelIsMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.ChainLaw

/-!
# Frozen definition: `LFMultigraph.walkLaw`

`Markov.chainLaw walkKernel (inl x)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The law of simple random walk from `x`, at the level of edge ends. -/
def walkLaw (x : V) : Measure (ℕ → G.State) :=
  Markov.chainLaw G.walkKernel (show G.State from Sum.inl x)

end LFMultigraph

end MatedCRTHarmonic

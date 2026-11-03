/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.WalkKernelIsMarkov at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.State
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateMeasurableSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StateVertex
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.StepMeasureIsProbability
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.WalkKernel

/-!
# Frozen definition: `LFMultigraph.instIsMarkovKernelStateWalkKernel`

`walkKernel` is a Markov kernel (Lean's automatic name of the candidate's anonymous instance).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

instance instIsMarkovKernelStateWalkKernel : IsMarkovKernel G.walkKernel :=
  ⟨fun s => by change IsProbabilityMeasure (G.stepMeasure _); infer_instance⟩

end LFMultigraph

end MatedCRTHarmonic

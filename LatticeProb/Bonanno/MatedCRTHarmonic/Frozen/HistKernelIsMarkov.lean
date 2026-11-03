/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.HistKernelIsMarkov at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.HistKernel

/-!
# Frozen definition: `Markov.histKernel_isMarkovKernel`

Copy in MC.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace Markov

variable {S : Type*} [MeasurableSpace S]

instance histKernel_isMarkovKernel (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (histKernel κ n) := by
  unfold histKernel; infer_instance

end Markov

end MatedCRTHarmonic

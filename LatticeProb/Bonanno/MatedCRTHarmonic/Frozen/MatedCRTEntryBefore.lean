/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTEntryBefore at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTFirstHit

/-!
# Frozen definition: `MatedCRT.entryBefore`

Non-junk by surjectivity and transience .
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- `T_z`: the last time `c` enters `U` before hitting `z` ([18] Lemma 2.4, [18]). -/
def entryBefore (c : C(ℝ, ℂ)) (U : Set ℂ) (z : ℂ) : ℝ := sSup {t : ℝ | t ≤ firstHit c z ∧ c t ∉ U}

end MatedCRT

end MatedCRTHarmonic

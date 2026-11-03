/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTDirectRel at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib

/-!
# Frozen definition: `MatedCRT.DirectRel`

Strict (`s < t`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- A direct `X`-identification of two times (DMS Lemma 8.9, DMS; `RouteM.directRel`). -/
def DirectRel (X : ℝ → ℝ) (s t : ℝ) : Prop :=
  s < t ∧ X s = X t ∧ ∀ u ∈ Ioo s t, X s < X u

end MatedCRT

end MatedCRTHarmonic

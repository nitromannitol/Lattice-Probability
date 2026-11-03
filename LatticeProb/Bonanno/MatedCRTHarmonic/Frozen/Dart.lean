/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.Dart at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.LFMultigraph

/-!
# Frozen definition: `LFMultigraph.Dart`

Edge ends `E × Bool` : a loop contributes two darts at its vertex.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- Edge ends (darts): `(e, false)` leaves `src e` towards `tgt e`, `(e, true)` leaves `tgt e` towards `src e`.
A loop contributes two darts at its vertex, a non-loop one dart at each end. -/
abbrev Dart (_G : LFMultigraph V E) : Type _ := E × Bool

end LFMultigraph

end MatedCRTHarmonic

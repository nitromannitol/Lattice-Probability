/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTIsEdge
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTEdge

/-!
# Frozen definition: `MatedCRT.IsLocallyFinite`

Non-vacuity anchor `ae_isLocallyFinite`; fails for `ε = 0` (S1X regression), so `0 < ε` carries content.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Local finiteness of the ε-mated-CRT map of `ω`: every vertex meets finitely many edges (almost sure for the
Brownian pair, `ae_isLocallyFinite`). -/
def IsLocallyFinite (ε : ℝ) (ω : Path2) : Prop :=
  ∀ x : ℤ, {e : Edge ε ω | e.1.1 = x ∨ e.1.2.1 = x}.Finite

end MatedCRT

end MatedCRTHarmonic

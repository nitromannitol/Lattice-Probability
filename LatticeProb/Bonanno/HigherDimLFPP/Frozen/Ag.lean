/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.Ag at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Vg
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Energy
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.GCov
import LatticeProb.Bonanno.LQGDimension.Statement.Defs

/-!
# Frozen definition: `Ag`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.6).  The expected supremum is the supremum over finite subfamilies of expected
maxima, the convention of `LQGDimension.aE` (equal to `E sup` for the continuous separable process).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPP

/-- `E sup_{f ∈ V_n(E)} (G(f) - E(f))`, as an extended real: the supremum over finite subfamilies
`F` of `E max_{f ∈ F} (G(f) - E(f))` for the centered Gaussian vector with covariance `gCov`. -/
def Ag (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) : EReal :=
  ⨆ F : Finset (Vg E n),
    ((LQGDimension.gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g)
      (fun f => -energy (f : ℝ → E)) : ℝ) : EReal)

end HigherDimLFPP

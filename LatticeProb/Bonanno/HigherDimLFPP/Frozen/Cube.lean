/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.Cube at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Rd

/-!
# Frozen definition: `cube`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1: `U = (-2,2)^d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPP

/-- `U = (-2, 2)^d`. -/
def cube (d : ℕ) : Set (Rd d) := {z | ∀ i, |z i| < 2}

end HigherDimLFPP

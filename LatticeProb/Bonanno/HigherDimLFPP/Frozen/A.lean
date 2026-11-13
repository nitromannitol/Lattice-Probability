/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Rd
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Ag

/-!
# Frozen definition: `A`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPP

/-- `A_{n,d} = E sup_{f ∈ V_{n,d}} (G_d(f) - E(f))` (1.6), with `V_{n,d} = V_n(ℝ^{d-1})`. -/
def A (n d : ℕ) : EReal := Ag (Rd (d - 1)) n

end HigherDimLFPP

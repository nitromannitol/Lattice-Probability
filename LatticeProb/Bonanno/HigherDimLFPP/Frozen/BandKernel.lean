/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.BandKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.ScaleKernel
import Mathlib.Algebra.Order.Group.Indicator

/-!
# Frozen definition: `bandKernel`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1): the integrand of `H_{a,b}(z) = ∫_a^b ∫ K_t(z - y) W(dy, dt)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLFPP

/-- `k_{a,b,z}(t, y) = 1_{(a,b)}(t) K_t(z - y)`, so that `H_{a,b}(z) = W(k_{a,b,z})` (1.1). -/
def bandKernel {d : ℕ} (κ : Rd d → ℝ) (a b : ℝ) (z : Rd d) : ℝ × Rd d → ℝ :=
  fun p => (Ioo a b).indicator (fun t => scaleKernel κ t (z - p.2)) p.1

end HigherDimLFPP

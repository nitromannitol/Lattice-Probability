/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.BandVec at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.BandKernel
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.WN

/-!
# Frozen definition: `bandVec`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.1).  The junk value `0` is excluded for admissible kernels and `0 < a < b` by the
frozen sanity theorem `bandVec_norm_sq` (`‖bandVec‖² = log(b/a)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPP

/-- The element `k_{a,b,z}` of `L²(ℝ × ℝ^d)` (junk `0` if not square integrable). -/
def bandVec {d : ℕ} (κ : Rd d → ℝ) (a b : ℝ) (z : Rd d) : WN d := by
  classical
  exact if h : MemLp (bandKernel κ a b z) 2 volume then h.toLp _ else 0

end HigherDimLFPP

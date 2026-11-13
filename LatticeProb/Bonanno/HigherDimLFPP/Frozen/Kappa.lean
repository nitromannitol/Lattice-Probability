/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.Kappa at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.A
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.PNat.Basic

/-!
# Frozen definition: `kappa`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPP

/-- `κ_d = inf_{n ≥ 1} A_{n,d} / (n log 2)` (1.7).  Finiteness of `A_{n,d}` and the facts that this
infimum is a limit and is positive are conclusions of `theorem11`. -/
def kappa (d : ℕ) : ℝ := ⨅ n : ℕ+, (A n d).toReal / ((n : ℝ) * Real.log 2)

end HigherDimLFPP

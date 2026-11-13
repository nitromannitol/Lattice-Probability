/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.WN at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Rd
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Frozen definition: `WN`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1 ("white noise W on ℝ^d × (0,∞) with Lebesgue control measure").  Ruling H10:
the index space is `L²(ℝ × ℝ^d)` (time first); only `t > 0` enters through the kernels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPP

/-- The white-noise index space `L²(ℝ × ℝ^d)` (time coordinate first). -/
abbrev WN (d : ℕ) : Type := Lp ℝ 2 (volume : Measure (ℝ × Rd d))

end HigherDimLFPP

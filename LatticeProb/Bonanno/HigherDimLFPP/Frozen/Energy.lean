/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.Energy at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Frozen definition: `energy`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPP

/-- The energy `E(f) = ½ ∫₀¹ |f'(x)|² dx` (1.4). -/
def energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) : ℝ :=
  (1 / 2) * ∫ x in (0 : ℝ)..1, ‖deriv f x‖ ^ 2

end HigherDimLFPP

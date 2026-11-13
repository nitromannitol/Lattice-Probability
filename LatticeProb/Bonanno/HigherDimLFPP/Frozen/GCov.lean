/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.GCov at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Frozen definition: `gCov`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPP

/-- The covariance (1.5) of `G_d`: `Cov(G_d(f), G_d(g)) = π ∫₀¹ (|f| + |g| - |f - g|) dx`. -/
def gCov {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : ℝ → E) : ℝ :=
  Real.pi * ∫ x in (0 : ℝ)..1, (‖f x‖ + ‖g x‖ - ‖f x - g x‖)

end HigherDimLFPP

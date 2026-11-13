/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.LfppLength at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Rd
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Frozen definition: `lfppLength`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.2) ("integrals count arclength with multiplicity").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPP

/-- The LFPP length `∫_P e^{ζ φ(z)} |dz| = ∫₀¹ e^{ζ φ(γ t)} |γ'(t)| dt` (arclength with
multiplicity). -/
def lfppLength {d : ℕ} (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.exp (ζ * φ (γ t)) * ‖deriv γ t‖

end HigherDimLFPP

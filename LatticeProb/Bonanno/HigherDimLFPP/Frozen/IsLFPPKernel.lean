/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.IsLFPPKernel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Rd
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Frozen definition: `IsLFPPKernel`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1: "κ : ℝ^d → [0,∞) a smooth, compactly supported radial function with ‖κ‖_{L²} = 1".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPP

/-- The fixed kernel `κ` of (1.1): smooth (`C^∞`: `((⊤ : ℕ∞) : WithTop ℕ∞)`, not analytic),
nonnegative, compactly supported, radial, with `∫ κ² = 1`. -/
structure IsLFPPKernel {d : ℕ} (κ : Rd d → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ
  nonneg : ∀ z, 0 ≤ κ z
  hasCompactSupport : HasCompactSupport κ
  radial : ∀ z w : Rd d, ‖z‖ = ‖w‖ → κ z = κ w
  integral_sq : ∫ z, κ z ^ 2 = 1

end HigherDimLFPP

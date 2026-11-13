/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.BandVecNormSq at commit fdb5cad; only the module paths of local imports are changed. -/
-- FROZEN_ANCHOR_PREFIX_BEGIN
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.BandVec
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPKernel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LatticeProb.Bonanno.HigherDimLFPP.Field.BandVec

/-!
# Frozen theorem: `bandVec_norm_sq`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1: "In particular, Var H_{ε,1}(z) = log ε^{-1}".  Sanity theorem: `bandVec` is not
its junk value, and the variance normalization of (1.1) holds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- For an admissible kernel and `0 < a < b`, `k_{a,b,z}` is square integrable and
`‖k_{a,b,z}‖² = log(b/a)`, i.e. `Var H_{a,b}(z) = log(b/a)`. -/
theorem bandVec_norm_sq : ∀ d : ℕ, 1 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ a b : ℝ, 0 < a → a < b → ∀ z : Rd d,
      MemLp (bandKernel κ a b z) 2 volume ∧ ‖bandVec κ a b z‖ ^ 2 = Real.log (b / a) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPP.bandVec_norm_sq_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPP
-- FROZEN_ANCHOR_SUFFIX_END

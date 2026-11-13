/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.IsAdmissiblePath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.Cube
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.E1
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Order.Fin.Basic

/-!
# Frozen definition: `IsAdmissiblePath`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.2).  Ruling H8: piecewise `C¹` paths (as in `LQGDimension` and DGZ); source App. A.1
shows they give the same infimum as rectifiable paths.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLFPP

/-- An admissible path in (1.2): a continuous, piecewise continuously differentiable path
`γ : [0,1] → U` from `0` to `e₁`.  Piecewise `C¹` means that there is a partition
`0 = t₀ < ⋯ < t_k = 1` such that `γ` is `C¹` on each closed piece. -/
structure IsAdmissiblePath (d : ℕ) (γ : ℝ → Rd d) : Prop where
  source : γ 0 = 0
  target : γ 1 = e₁ d
  mapsTo : MapsTo γ (Icc 0 1) (cube d)
  continuousOn : ContinuousOn γ (Icc 0 1)
  piecewise_contDiff : ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t ∧ t 0 = 0 ∧
    t (Fin.last k) = 1 ∧ ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ))

end HigherDimLFPP

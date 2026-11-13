/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Frozen.Vg at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Interval.Set.Defs

/-!
# Frozen definition: `Vg`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1, the space `V_{n,d}` (with `E = ℝ^{d-1}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLFPP

/-- `V_n(E)`: the functions `f : [0,1] → E` that vanish at `0` and `1` and are affine on every
dyadic interval `[k 2⁻ⁿ, (k+1) 2⁻ⁿ]` (closed pieces, so `f` is continuous), extended by zero
outside `[0,1]`. -/
def Vg (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) : Set (ℝ → E) :=
  {f | f 0 = 0 ∧ f 1 = 0 ∧ (∀ x, x ∉ Icc (0 : ℝ) 1 → f x = 0) ∧
    ∀ k : ℕ, k < 2 ^ n → ∃ α β : E,
      ∀ x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n), f x = x • α + β}

end HigherDimLFPP

import LatticeProb.Prob.Percolation.GreenColumn
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Classical

namespace LatticeProb.Percolation

noncomputable section

/-- The continuum Green function with positive scalar conductivity, on punctured space. -/
def continuumGreen (d : ℕ) (_hd : 2 ≤ d) (κ : {a : ℝ // 0 < a})
    (z : {x : EuclideanSpace ℝ (Fin d) // x ≠ 0}) : ℝ :=
  if d = 2 then
    -Real.log ‖z.val‖ / (2 * Real.pi * κ.val)
  else
    (Real.Gamma ((d : ℝ) / 2 - 1) /
      (4 * Real.rpow Real.pi ((d : ℝ) / 2) * κ.val)) *
        Real.rpow ‖z.val‖ (2 - (d : ℝ))

end
end LatticeProb.Percolation

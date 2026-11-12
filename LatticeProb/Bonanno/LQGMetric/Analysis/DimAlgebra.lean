/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Analysis.DimAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The key algebra of the `d_γ` chain (node DIM.ALG)

Real-number lemmas for route B of decision D12 (`decisions/DEC-A.md`, D-A1, steps 1–6;
`blueprint/Dimension.md`, "Key algebra"). Notation: `γ > 0`, `d = d_γ`, `ξ = γ/d`,
`Q = 2/γ + γ/2`, `a = γ²/4`. The function
`g = 1 − ξQ + ξ²/2 = 1 − 2/d − γ²/(2d) + γ²/(2d²)` is the right side of
Ding–Gwynne, arXiv:1807.01072, eq. (1.7b) / `eqn-exponent-mono` (`metric-comparison-final.tex`
l. 775–779). The statements are elementary identities and inequalities that the sources state
without proof (GM `uniqueness-final.tex` l. 1056; DFGPS l. 2453, 2531; DEC-A step 5–6);
own elementary proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric
namespace Analysis

/-- DEC-A step 3: `γ' := min(ξ, ξ₀, 1)/2` lies in `(0,2)` and below `ξ` and `ξ₀`. -/
lemma auxGamma_spec {ξ ξ₀ : ℝ} (hξ : 0 < ξ) (hξ₀ : 0 < ξ₀) :
    0 < min (min ξ ξ₀) 1 / 2 ∧ min (min ξ ξ₀) 1 / 2 < 2 ∧ min (min ξ ξ₀) 1 / 2 < ξ ∧
      min (min ξ ξ₀) 1 / 2 < ξ₀ := by
  have h1 : 0 < min (min ξ ξ₀) 1 := lt_min (lt_min hξ hξ₀) one_pos
  have h2 : min (min ξ ξ₀) 1 ≤ ξ := (min_le_left _ _).trans (min_le_left _ _)
  have h3 : min (min ξ ξ₀) 1 ≤ ξ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have h4 : min (min ξ ξ₀) 1 ≤ 1 := min_le_right _ _
  refine ⟨by positivity, by linarith, by linarith, by linarith⟩

end Analysis
end LQGMetric

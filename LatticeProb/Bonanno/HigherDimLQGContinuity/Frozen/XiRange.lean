/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGContinuity.Frozen.XiRange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.Frozen.DistExp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Frozen definition: `xiRange`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N3, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): (1.5), l. 74–81 (the Weyl parameter
`0 < ξ < ξ_c`), l. 89–92 and 100 (compact parameter intervals `J ⋐ [0, ξ_c)`, including `ξ = 0`, the Euclidean
endpoint `D⁰` of l. 36). The parameter range `{0} ∪ {ξ > 0 : Q(ξ) > √(2d)}` with `Q = HigherDimLQGMetric.distExp d`
(ruling N4); by `prop18` it is `[0, ξ_c)`, `ξ_c ∈ (0, ∞]`, the image of `[0, √(2d))` under the parametrization.
Defined without `sSup`, so no junk value of `sSup` on `ℝ` can shrink the range. `distExp` is a
`Classical.choose` with junk value `0`; the sealed `HigherDimLQGMetric.distExp_spec` excludes the junk branch
for `d ≥ 2`, `ξ > 0`, and `distExp` is evaluated here only at `ξ > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The Weyl-parameter range of Theorem 1.1: `{0} ∪ {ξ > 0 : √(2d) < Q(ξ)}` (`= [0, ξ_c)` by `prop18`). -/
def xiRange (d : ℕ) : Set ℝ := insert 0 {ξ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ}

end HigherDimLQGContinuity

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# DG Lemma 3.3, deterministic part: (3.6) ⇒ (3.7) (task P2-DG3A, WP-118)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.3 (`lem-measure-scale`,
DG:1014–1032). (3.6): a.s. `μ_ĥ(X) = δ^{2+γ²/2} ∫_{δ⁻¹(X−b)} e^{γ ĥ_δ(δ·+b)} dμ_{(ĥ−ĥ_δ)(δ·+b)}`
for all Borel `X`. (3.7): with `T̄ := δ^{−2−γ²/2} exp(−max_U ĥ_δ)`,
`D^ε_ĥ(z,w;U) ≤ D^{T̄ε}_{(ĥ−ĥ_δ)(δ·+b)}(δ⁻¹(z−b), δ⁻¹(w−b); δ⁻¹(U−b))`, and the reverse
inequality with `T̲ := δ^{−2−γ²/2} exp(−min_U ĥ_δ)`. DG's proof (DG:1033–1036): "(3.7) follows
from (3.6) applied to Euclidean balls contained in `U`."

This file proves that deterministic step for arbitrary measures `μ` (for `μ_ĥ`) and `ν` (for
`μ_{(ĥ−ĥ_δ)(δ·+b)}`) related by (3.6), a field `φ` (for `ĥ_δ`) with `m ≤ φ ≤ M` on `Ū`, scale
`a > 0` (for `δ`), shift `b`, exponent `q` (for `2 + γ²/2`):

* `dgLGD_affine_le` — LGD under the affine change of coordinates `y ↦ a y + b`;
* `dg_lemma33_dist` — (3.7), both inequalities.

Convention (proposed deviation DG3A-1): DG's `T̄, T̲` contain `exp(−max ĥ_δ)`, `exp(−min ĥ_δ)`;
(3.6) has the weight `e^{γ ĥ_δ}`, so the constants that (3.6) gives are
`δ^{−2−γ²/2} e^{−γ max ĥ_δ}`, `δ^{−2−γ²/2} e^{−γ min ĥ_δ}`; we use these (`φ = ĥ_δ`, weight
`e^{γφ}`), i.e. we read DG's formula with the factor `γ` in the exponent. (3.6) itself needs the
LQG measure `μ_ĥ` (DG Lemma 3.1) and the coordinate change formula (DS Prop 2.1, node F.AFFINE),
not formalized here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- the affine map `y ↦ a y + b` -/
def affineC (a : ℝ) (b y : ℂ) : ℂ := (a : ℂ) * y + b

lemma continuous_affineC (a : ℝ) (b : ℂ) : Continuous (affineC a b) :=
  (continuous_const.mul continuous_id).add continuous_const

end DG
end LQGMetric

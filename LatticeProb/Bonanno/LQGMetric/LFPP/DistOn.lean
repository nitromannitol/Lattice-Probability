/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.DistOn at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP

/-!
# The LFPP distance with a general density, internal to a set

Task P2-LFPP. For `φ : ℂ → ℝ` and `S ⊆ ℂ`, `lfppDOn ξ φ S z w` is the infimum of
`∫₀¹ e^{ξ φ(P)} |P'|` over piecewise C¹ paths `P : z → w` staying in `S` (GM (1.4),
`uniqueness-final.tex` l. 216–220, for `S = ℂ`; DFGPS l. 285, `lqg-metric-estimates-final.tex`,
for `S = [0,1]²`). Both `lfppDistE` (Statement) and DFGPS's `lfppCrossIn` (Blueprint) are
instances. Elementary properties: triangle inequality, symmetry, `D(z,z) = 0`, segment bound,
chain bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ}

theorem segPath_mem (hS : Convex ℝ S) {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : segPath z w u ∈ S :=
  hS.add_smul_sub_mem hz hw hu

/-- the cost of the straight segment from `a` to `b` -/
def segCost (ξ : ℝ) (φ : ℂ → ℝ) (a b : ℂ) : ℝ≥0∞ := lfppLen ξ φ (segPath a b)

end LFPP
end LQGMetric

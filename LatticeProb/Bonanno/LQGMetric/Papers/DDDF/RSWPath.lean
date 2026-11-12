/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWPath at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

/-!
Task P2-DDDFRSW. DDDF (`tightness.tex` l. 794, 800; DF arXiv:1809.02607 DF:650–670) use that if a
crossing `π` of a domain contains a sub-arc crossing a smaller domain, then the crossing length
of the smaller domain is at most the length of `π`. Here: if a piecewise-C¹ path `P` has a
sub-arc `P([s,t])` (either time direction) in `K` from `A` to `B`, then
`crossLenIn ξ f K A B ≤ lfppLen ξ f P` (sub-path and reversal from `LFPP.PathOps`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open LFPP

variable {ξ : ℝ} {f : ℂ → ℝ}

theorem lfppLen_const (z : ℂ) : lfppLen ξ f (fun _ => z) = 0 := by
  simp [lfppLen]

end DDDF
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P29Second at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatKernelSquareCK2
import LatticeProb.Bonanno.LQGMetric.Field.ExistKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DDDF (arXiv:1904.08021), `tightness.tex:1576–1588`: for `x, x' ∈ U`, `d = d(U, D^c)`,
`φ²_t(x) = √π ∫_0^{1−t} ∫_{D^c} p_{(t+s)/2}(x − y) W(dy, ds)` satisfies
`E(φ²_t(x) − φ²_t(x'))² ≤ C|x − x'|` and `E φ²_t(x)² ≤ C`, uniformly in `t`.

With `r = (t + s)/2` the variances are `2π ∫_{t/2}^{1/2} F(r) dr` with
`F(r) = ∫_{D^c} (p_r(x,y) − p_r(x',y))² dy` (resp. `p_r(x,y)²`), so it suffices to bound
`∫_0^∞ F(r) dr`, which we do here in `ℝ≥0∞`. DDDF's proof: split the time integral; for large
`r` use `∫_{ℝ²} (p_r(x−·) − p_r(x'−·))² = 2(p_{2r}(0) − p_{2r}(x−x')) ≤ |x−x'|²/(8πr²)`
(`GFFExist.integral_sq_heatKernel_sub_le`, via `1 − e^{−z} ≤ z`), for small `r` use
`|y − x|, |y − x'| ≥ d` on `D^c`. DDDF split at `r = √|x−x'|`; we split at `r = |x − x'|`,
which gives the stated `O(|x − x'|)` directly (the `√` split only gives `O(√|x−x'|)` for the
small-time part).
-/

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace LQGMetric
namespace HeatSq

/-- `∫ (p_r(x,y) − p_r(x',y))² dy ≤ |x − x'|²/(8πr²)`. -/
lemma integral_sq_heatKernel_sub_le' {r : ℝ} (hr : 0 < r) (x x' : ℂ) :
    ∫ y, (heatKernel r x y - heatKernel r x' y) ^ 2 ≤ ‖x - x'‖ ^ 2 / (8 * π * r ^ 2) := by
  rw [← integral_add_right_eq_self (fun y => (heatKernel r x y - heatKernel r x' y) ^ 2) x']
  refine le_of_eq_of_le ?_ (GFFExist.integral_sq_heatKernel_sub_le r hr (x - x'))
  congr 1; funext y
  unfold heatKernel
  congr 4
  · congr 2; ring_nf
  · congr 2; ring_nf

end HeatSq
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricInternal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricIsLengthSpace

/-! Scratch freeze split of SLUMetric.lean:158. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- DG l. 424–429: the internal metric `D (·, ·; Y)` of `D` on `Y ⊆ ℂ`, on its carrier `Y × Y`:
the infimum of the `D`-lengths of curves in `Y` from `x` to `y` (`∞` if there is none). -/
def internal (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b) (_ : ∀ t ∈ Icc a b, P t ∈ Y)
    (_ : P a = (p.1 : ℂ)) (_ : P b = (p.2 : ℂ)), D.len P a b
end LSCMetric
end SupercriticalLQGUniqueness

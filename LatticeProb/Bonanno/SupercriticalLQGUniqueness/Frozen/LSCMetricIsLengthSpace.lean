/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricIsLengthSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricLen

/-! Scratch freeze split of SLUMetric.lean:151. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- DG l. 421, repaired at pairs at infinite distance (ruling D1): `(ℂ, D)` is a length space if
for all `x, y` with `D (x, y) < ∞` and every `ε > 0` there is a curve from `x` to `y` of
`D`-length at most `D (x, y) + ε`. Equivalently (`isLengthSpace_iff_eq_iInf`), `D (x, y)` is the
infimum of the `D`-lengths of curves from `x` to `y`, with `inf ∅ = ∞` (Pfeffer, Def. 1.5). -/
def IsLengthSpace (D : LSCMetric) : Prop :=
  ∀ x y : ℂ, D (x, y) < ∞ → ∀ ε : ℝ, 0 < ε →
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧ P a = x ∧ P b = y ∧
      D.len P a b ≤ D (x, y) + ENNReal.ofReal ε
end LSCMetric
end SupercriticalLQGUniqueness

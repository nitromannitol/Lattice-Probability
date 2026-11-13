/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.LSCMetricIsCurve at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInstEMetricSpace

/-! Scratch freeze split of SLUMetric.lean:138. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- DG l. 413: `P` restricted to `[a, b]` is a curve in `(ℂ, D)`, i.e. `a ≤ b` and `P` is
continuous on `[a, b]` for the topology of the extended metric `D`. The values of `P` outside
`[a, b]` play no role. -/
def IsCurve (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn (D.pt ∘ P) (Icc a b)
end LSCMetric
end SupercriticalLQGUniqueness

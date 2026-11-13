/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.AroundDist at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.AcrossDist

/-! Scratch freeze split of SLUMetric.lean:212. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- DG Definition 1.11 (l. 556): `D (around A)`, the infimum of the `D`-lengths of curves in `A`
which disconnect the inner and outer boundaries of `A` (`∞` if there is none). -/
def aroundDist (D : LSCMetric) (A : EuclideanAnnulus) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b) (_ : ∀ t ∈ Icc a b, P t ∈ A.toSet)
    (_ : Disconnects (P '' Icc a b) A.innerBoundary A.outerBoundary), D.len P a b
end SupercriticalLQGUniqueness

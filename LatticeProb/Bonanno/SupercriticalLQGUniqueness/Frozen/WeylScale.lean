/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Frozen.WeylScale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.AroundDist

/-! Scratch freeze split of SLUMetric.lean:221. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- DG (1.11), l. 448–452: `(e^{ξ f} · D) (z, w)`, the infimum over `D`-rectifiable curves `P`
from `z` to `w` parametrized by `D`-length (unit speed on `[0, L]`, `L = len (P; D)`) of
`∫₀ᴸ e^{ξ f (P t)} dt`, with `inf ∅ = ∞`. -/
def weylScale (ξ : ℝ) (f : C(ℂ, ℝ)) (D : LSCMetric) (p : ℂ × ℂ) : ℝ≥0∞ :=
  ⨅ (P : ℝ → ℂ) (L : ℝ) (_ : D.IsCurve P 0 L) (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (_ : P 0 = p.1) (_ : P L = p.2), ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))
end SupercriticalLQGUniqueness

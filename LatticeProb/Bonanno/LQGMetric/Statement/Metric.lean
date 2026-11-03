/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Statement.Metric at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Analysis.ConstantSpeed
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import LatticeProb.Bonanno.LQGMetric.Metric.CurveLength
import LatticeProb.Bonanno.LQGMetric.Metric.LengthSpace

/-!
# Statement layer, part 3: continuous metrics, lengths, internal metrics, Weyl scaling

`FOUNDATIONS.md` §4 and §5 (blocks copied verbatim). Source: GM (arXiv:1905.00383v3,
`literature/src/1905.00383/uniqueness-final.tex`) §1.2, l. 255–289 (distance between sets,
curves, `len(P; 𝔡)`, internal metric (1.5), length spaces, continuous metrics and the local
uniform topology), l. 300–302 (Weyl scaling (1.6)), l. 230 and 298 ("a.s. determined by"),
l. 230 ("converge in probability w.r.t. the local uniform topology on ℂ × ℂ").
The metric geometry is P1-MG's general layer `LQGMetric.MetricGeometry`
(`Metric/CurveLength.lean`, `Metric/LengthSpace.lean`) applied to `ℂ` carrying the metric `D`
(the type synonym `ContMetric.Space`, D5). Decisions D4, D5, D8; deviations F8, F9, F10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-! ## §4. Continuous metrics, convergence in probability, "determined by" -/

/-- `d` is a (finite) metric on `ℂ`, written as a function on `ℂ × ℂ` -/
structure IsMetricFn (d : ℂ × ℂ → ℝ) : Prop where
  self_eq_zero : ∀ x, d (x, x) = 0
  eq_of_eq_zero : ∀ x y, d (x, y) = 0 → x = y
  symm : ∀ x y, d (x, y) = d (y, x)
  triangle : ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z)

/-- a continuous metric on ℂ: a metric, continuous as a function (it lives in `C(ℂ×ℂ,ℝ)`),
whose small balls are Euclidean-small; together: it induces the Euclidean topology. -/
structure IsContinuousMetric (d : C(ℂ × ℂ, ℝ)) : Prop extends IsMetricFn d where
  euclidean_of_small : ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, d (x, y) < δ → ‖x - y‖ < ε

/-- the space of continuous metrics on ℂ, local uniform (= compact-open) topology, Borel σ-alg. -/
def ContMetric : Type := {d : C(ℂ × ℂ, ℝ) // IsContinuousMetric d}
instance : MeasurableSpace ContMetric := Subtype.instMeasurableSpace
instance : TopologicalSpace ContMetric := instTopologicalSpaceSubtype

section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- a.s. determined by `X`: `Y = F ∘ X` a.s. for a measurable `F` -/
def AEDeterminedBy {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Y : Ω → β) (X : Ω → α) (P : Measure Ω) : Prop :=
  ∃ F : α → β, Measurable F ∧ Y =ᵐ[P] F ∘ X

/-- convergence in probability w.r.t. the local uniform topology on functions ℂ × ℂ → ℝ -/
def TendstoInProbLU {ι : Type*} (P : Measure Ω) (X : ι → Ω → ℂ × ℂ → ℝ) (l : Filter ι)
    (Y : Ω → ℂ × ℂ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ →
    Tendsto (fun i => P {ω | ENNReal.ofReal δ ≤
      ⨆ p ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) R,
        edist (X i ω p) (Y ω p)}) l (𝓝 0)

end

/-! ## §5. Curves, lengths, internal metrics, Weyl scaling -/

/-- ℂ carrying the metric `D` -/
def ContMetric.Space (_D : ContMetric) : Type := ℂ
/-- the identity `ℂ → D.Space` -/
def ContMetric.pt (D : ContMetric) : ℂ → D.Space := id
instance (D : ContMetric) : MetricSpace D.Space where
  dist x y := D.1 (x, y)
  dist_self x := D.2.self_eq_zero x
  dist_comm x y := D.2.symm x y
  dist_triangle x y z := D.2.triangle x y z
  eq_of_dist_eq_zero {x y} h := D.2.eq_of_eq_zero x y h

/-- `len(P; D)` on `[a, b]` -/
def ContMetric.len (D : ContMetric) (P : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  MetricGeometry.curveLength (D.pt ∘ P) a b
/-- internal metric `D(z, w; U)` (GM (1.5), values in [0,∞]) -/
def ContMetric.internal (D : ContMetric) (U : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  MetricGeometry.internalEDist (X := D.Space) (D.pt '' U) (D.pt z) (D.pt w)
/-- `(ℂ, D)` is a length space -/
def ContMetric.IsLength (D : ContMetric) : Prop := MetricGeometry.IsLengthSpace D.Space

/-- Weyl scaling `(e^{ξ f}·D)(z,w) := inf ∫_0^{len(P;D)} e^{ξ f(P(t))} dt` over continuous paths
from z to w parametrized by D-length (GM (1.6)) -/
def weylScale (ξ : ℝ) (f : C(ℂ, ℝ)) (D : ContMetric) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (L : ℝ) (P : ℝ → ℂ) (_ : 0 ≤ L) (_ : ContinuousOn (D.pt ∘ P) (Icc 0 L))
    (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = z) (_ : P L = w),
    ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))

end LQGMetric

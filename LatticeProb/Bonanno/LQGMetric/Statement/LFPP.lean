/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Statement.LFPP at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Statement layer, part 6: Liouville first passage percolation and `𝔞_ε`

`FOUNDATIONS.md` §7 (block copied verbatim). Source: GM (arXiv:1905.00383v3,
`literature/src/1905.00383/uniqueness-final.tex`) l. 216–224:
(1.4) "D_h^ε(z,w) := inf_{P : z → w} ∫_0^1 e^{ξ h*_ε(P(t))} |P'(t)| dt where the infimum is over
all piecewise continuously differentiable paths from z to w"; "Let 𝔞_ε be the median of the
D_h^ε-distance between the left and right boundaries of the unit square in the case when h is a
whole-plane GFF normalized so that its circle average over ∂𝔻 is zero."
The path structure follows LQGDimension's `IsAdmissiblePath` (general endpoints, no domain
constraint). Decision D7; deviations F6, F7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- piecewise C¹ path `[0,1] → ℂ` from `z` to `w` (as LQGDimension.IsAdmissiblePath, without the
domain constraint and with general endpoints) -/
structure IsPiecewiseC1Path (P : ℝ → ℂ) (z w : ℂ) : Prop where
  source : P 0 = z
  target : P 1 = w
  continuousOn : ContinuousOn P (Icc 0 1)
  piecewise : ∃ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t ∧ t 0 = 0 ∧
    t (Fin.last k) = 1 ∧ ∀ i : Fin k, ContDiffOn ℝ 1 P (Icc (t i.castSucc) (t i.succ))

/-- `∫₀¹ e^{ξ φ(P(t))} |P'(t)| dt` in [0,∞] -/
def lfppLen (ξ : ℝ) (φ : ℂ → ℝ) (P : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.exp (ξ * φ (P t)) * ‖deriv P t‖)
/-- `D^ε_h(z,w)` (GM (1.4)) -/
def lfppDistE (ξ ε : ℝ) (h : DistC) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ P : {P : ℝ → ℂ // IsPiecewiseC1Path P z w}, lfppLen ξ (heatMollify ε h) P.1
/-- `D^ε_h` as a real function on `ℂ × ℂ` (`toReal` junk `0` where `D^ε_h = ∞`) -/
def lfppDist (ξ ε : ℝ) (h : DistC) : ℂ × ℂ → ℝ := fun p => (lfppDistE ξ ε h p.1 p.2).toReal

/-- the left side `{0} × [0,1]` of the unit square -/
def leftSide : Set ℂ := {z | z.re = 0 ∧ 0 ≤ z.im ∧ z.im ≤ 1}
/-- the right side `{1} × [0,1]` of the unit square -/
def rightSide : Set ℂ := {z | z.re = 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}
/-- `D^ε_h(left side, right side)` -/
def lfppCross (ξ ε : ℝ) (h : DistC) : ℝ :=
  (⨅ z ∈ leftSide, ⨅ w ∈ rightSide, lfppDistE ξ ε h z w).toReal

open Classical in
/-- the law of the whole-plane GFF normalized by `h_1(0) = 0`, chosen; junk `0` -/
def normGFFLaw : Measure DistC :=
  if hμ : ∃ μ : Measure DistC, IsProbabilityMeasure μ ∧ IsNormalizedWPGFF id μ then hμ.choose
  else 0
/-- lower median `inf {m : μ(X ≤ m) ≥ 1/2}` (outer measure: no measurability needed) -/
def lowerMedian {α : Type*} [MeasurableSpace α] (μ : Measure α) (X : α → ℝ) : ℝ :=
  sInf {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ μ {x | X x ≤ m}}
/-- `𝔞_ε` (GM l. 223) -/
def aEps (ξ ε : ℝ) : ℝ := lowerMedian normGFFLaw (lfppCross ξ ε)

end LQGMetric

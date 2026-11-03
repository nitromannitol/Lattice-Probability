/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.LQG.WedgeProcess at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.QuantumZipper.SLE.Defs
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Independence.Basic

/-!
# The α-quantum wedge: lateral part, radial process, and wedge field

Definitions for Sheffield's α-quantum wedge (Section 1.6 / FOUNDATIONS.md §6), valid in the
range `α < Q` (STATEMENT_SPEC.md B1). A wedge field on `ℍ` is `h = h† + A_{-log|·|}` where
`h†` is the lateral part (the field minus its semicircle averages around `0`) and `A` is the
two-sided radial process: `A_t = B_t + (α - Q) t` for `t ≥ 0`, and for `t < 0`,
`A_t = B̃_{-t + s₀}` with `B̃_s = B'_s - (α - Q) s` and `s₀` the last zero of `B̃`
(i.e. `B̃` conditioned, via the last-exit decomposition, to stay positive). Here `B, B'` are
`√2` times independent standard Brownian motions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

/-- The lateral part `h† = h - h_{|·|}(0)` of a field sample: paired with a measure `μ`, it is
`⟨h, μ⟩ - ∫ h_{|z|}(0) dμ(z)`, where `h_r(0)` is the regularized semicircle average
`radAvgReg`. In the paper, `h†` is independent of the additive constant of `h`. -/
def lateralPart (x : FieldSample) : FieldSample :=
  fun μ => evalReg x μ - ∫ z, radAvgReg x ‖z‖ ∂μ

/-- The wedge field `h = y + Q·(-log|·|) + A_{-log|·|}` paired with `μ`: `y` is the lateral part
(in the paper, an independent sample of `h†` for a free-boundary GFF on `ℍ`), and `A` is the
radial process, evaluated at the log-scale `-log|z|`. Note `Q·(-log|z|)` is the coordinate
change term: the paper's radial parametrization `A_t` includes the drift `(α-Q)t`, so that
the semicircle average of `h` at radius `e^{-t}` is `A_t + Q t`. -/
def wedgeField (y : FieldSample) (A : ℝ → ℝ) (Q : ℝ) : FieldSample :=
  fun μ => y μ + ∫ z, (Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖)) ∂μ

/-- The last zero `sup {s ≥ 0 : b s = 0}` of a path `b` (junk value per `sSup` if the set is
empty or unbounded). For `B̃_s = B'_s - (α-Q)s` with `α < Q`, this is a.s. finite. -/
def lastZero (b : ℝ → ℝ) : ℝ := sSup {s | 0 ≤ s ∧ b s = 0}

/-- The two-sided wedge radial path built from two paths `b, b'` (standard Brownian paths; the
paper's `B = √2 b`, `B' = √2 b'`): for `t ≥ 0`, `A_t = √2 b_t + (α-Q)t`; for
`t < 0`, `A_t = B̃_{-t + s₀}` with `B̃_s = √2 b'_s - (α-Q)s` and `s₀ = lastZero B̃`. -/
def wedgePath (α Q : ℝ) (b b' : ℝ≥0 → ℝ) : ℝ → ℝ :=
  let Bt : ℝ → ℝ := fun s => Real.sqrt 2 * b' s.toNNReal - (α - Q) * s
  fun t => if 0 ≤ t then Real.sqrt 2 * b t.toNNReal + (α - Q) * t else Bt (-t + lastZero Bt)

/-- `A` is the radial process of an α-quantum wedge under `P`: it is `wedgePath α Q` applied
to the paths of two independent standard Brownian motions `B, B'`. -/
def IsWedgeProcess {Ω : Type*} [MeasurableSpace Ω] (α Q : ℝ) (A : ℝ → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  ∃ B B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧ IsBrownianReal B' P ∧
    IndepFun (pathOf B) (pathOf B') P ∧
    ∀ ω t, A t ω = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) t

/-- The wedge radial path starts at `0` when the forward path does. -/
theorem wedgePath_zero_of_start {α Q : ℝ} {b b' : ℝ≥0 → ℝ} (hb : b 0 = 0) :
    wedgePath α Q b b' 0 = 0 := by
  simp [wedgePath, hb]

end QuantumZipper

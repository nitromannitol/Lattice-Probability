/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Loewner.Forward at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Defs.Filter

/-!
# The forward centered Loewner flow

Driving functions are `W : ℝ → ℝ`, continuous (only `t ≥ 0` is used). The forward Loewner flow
`g_t` solves `dg_t(z) = 2/(g_t(z) - W_t) dt`, `g_0(z) = z`. We work throughout with the
**forward centered flow** `f_t = g_t − W_t`, written in centered integral form so that no
derivative of `W` is needed:
`f_t(z) = z - W_t + ∫_0^t 2/f_s(z) ds`.

See `FOUNDATIONS.md` §4 for the design. This file only contains definitions; the ODE theory
(existence, uniqueness, monotonicity of the imaginary part, ...) is in
`QuantumZipper/Proofs/Loewner/ForwardODE.lean`.
-/

noncomputable section

open MeasureTheory Set Filter Classical
open scoped Topology ENNReal NNReal

namespace QuantumZipper

/-- `IsForwardSol W z T u` says that `u : ℝ → ℂ` is a solution on `[0,T]` of the forward
centered flow `f_t = g_t − W_t` started at `f_0 = z`, i.e. `u` is continuous on `[0,T]`, never
vanishes there (so `z` has not yet been swallowed), and satisfies the centered integral
equation `u t = z - W t + ∫_0^t 2/u s ds`. -/
def IsForwardSol (W : ℝ → ℝ) (z : ℂ) (T : ℝ) (u : ℝ → ℂ) : Prop :=
  ContinuousOn u (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
    u t ≠ 0 ∧ u t = z - W t + ∫ s in (0 : ℝ)..t, 2 / u s

/-- The swallowing time of `z` under the forward flow driven by `W`: the supremum, in `ℝ≥0∞`,
of the `T ≥ 0` such that a solution of the centered forward flow exists on `[0,T]`. -/
def swallowTime (W : ℝ → ℝ) (z : ℂ) : ℝ≥0∞ :=
  sSup (ENNReal.ofReal '' {T : ℝ | 0 ≤ T ∧ ∃ u, IsForwardSol W z T u})

/-- The forward hull at time `T`: the points of `ℍ` already swallowed by time `T`. -/
def fwdHull (W : ℝ → ℝ) (T : ℝ) : Set ℂ := {z ∈ H | swallowTime W z ≤ ENNReal.ofReal T}

/-- The forward map `f_T(z)`: the value at time `T` of a chosen solution of the centered
forward flow on `[0,T]` started at `z`, if one exists, else the junk value `0`. -/
def fwdMap (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  if h : ∃ u, IsForwardSol W z T u then h.choose T else 0

/-- The inverse forward map: the unique `z' ∈ ℍ \ K_T` with `f_T(z') = w`, if such a unique
`z'` exists, else the junk value `0`. -/
def fwdMapInv (W : ℝ → ℝ) (T : ℝ) (w : ℂ) : ℂ :=
  if h : ∃! z', z' ∈ H \ fwdHull W T ∧ fwdMap W T z' = w then h.choose else 0

/-- The canonical branch of `log f_T'(z)`: minus the integral of `2/f_s(z)^2`. Its imaginary
part is, by definition, the continuous branch of `arg f_T'` vanishing at `∞`. -/
def logDerivFwd (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  -∫ s in (0 : ℝ)..T, 2 / (fwdMap W s z) ^ 2

/-- The image of the marked boundary point `0` under the forward flow at time `t`, i.e. the SLE
trace: `η(t) = lim_{y ↓ 0} f_t⁻¹(iy)`. -/
def trace (W : ℝ → ℝ) (t : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun y : ℝ => fwdMapInv W t (y * Complex.I)

end QuantumZipper

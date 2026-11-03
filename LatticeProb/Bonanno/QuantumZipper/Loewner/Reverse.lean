/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Loewner.Reverse at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Reverse centered Loewner flow

Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, Section 1. See `FOUNDATIONS.md` §4 for the design of this file.

The reverse centered Loewner flow started at `z` and driven by `W` is written in centered
integral form, `u_t = z - W_t - ∫_0^t 2/u_s ds`, so that no derivative of `W` is needed. Only
the *definitions* are in this file. Existence (for `z` in the upper half-plane `H`),
uniqueness, and the basic global properties of the flow are proved in
`QuantumZipper.Proofs.Loewner.ReverseODE`.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace QuantumZipper

/-- `u` is a solution on `[0,T]` of the reverse centered Loewner flow started at `z` and
driven by `W`: `u_t = z - W_t - ∫_0^t 2/u_s ds` with `u_t ∈ ℍ` throughout, for `t ∈ [0,T]`.
Written in centered integral form so that no derivative of `W` is needed.
`QuantumZipper.Proofs.Loewner.ReverseODE` shows a solution exists and is unique whenever
`0 < z.im` and `0 ≤ T`. -/
def IsReverseSol (W : ℝ → ℝ) (z : ℂ) (T : ℝ) (u : ℝ → ℂ) : Prop :=
  ContinuousOn u (Set.Icc 0 T) ∧ ∀ t ∈ Set.Icc 0 T,
    0 < (u t).im ∧ u t = z - W t - ∫ s in (0 : ℝ)..t, 2 / u s

open Classical in
/-- The value at time `T` of the reverse flow driven by `W`, started at `z`: `u T` for `u` the
(unique, when it exists) solution of `IsReverseSol W z T u`, and junk `0` if no solution
exists. `ReverseODE.lean` shows a solution always exists and is unique for `0 < z.im` and
`0 ≤ T`, so `revMap W T` then genuinely is the time-`T` reverse flow map, a conformal
bijection `H → H \ revHull W T`. -/
def revMap (W : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  if h : ∃ u, IsReverseSol W z T u then (Classical.choose h) T else 0

/-- The hull swallowed by the reverse flow by time `T`: the part of the upper half-plane `H`
missed by the image of `revMap W T`. In the paper's setting (§1.2–1.3), this is a compact
set cut off from `H` by a simple curve. -/
def revHull (W : ℝ → ℝ) (T : ℝ) : Set ℂ := H \ revMap W T '' H

/-- The boundary value of `revMap W T` at a real point `x`: the limit of `revMap W T (x + iy)`
as `y ↓ 0`. This is the genuine continuous boundary extension of the conformal map
`revMap W T` only in the paper's setting, where `revHull W T` is (bounded by) a simple curve;
otherwise (or if the limit fails to exist) `limUnder` returns an unspecified junk value. -/
def revMapBdry (W : ℝ → ℝ) (T : ℝ) (x : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun y : ℝ => revMap W T (x + y * I)

/-- The negative preimage `0₋` of the curve's base point `0` under the boundary extension of
`revMap W T`, i.e. `sup {x < 0 : revMapBdry W T x = 0}`. Only genuinely a point with
`revMapBdry W T (zeroMinus W T) = 0` and `zeroMinus W T < 0 < zeroPlus W T` in the paper's
setting, where `revHull W T` is a simple curve through `0` (Theorem 1.3). -/
def zeroMinus (W : ℝ → ℝ) (T : ℝ) : ℝ := sSup {x | x < 0 ∧ revMapBdry W T x = 0}

/-- The positive preimage `0₊` of the curve's base point `0` under the boundary extension of
`revMap W T`, i.e. `inf {x > 0 : revMapBdry W T x = 0}`. Meaningful in the same sense, and
under the same hypotheses, as `zeroMinus`. -/
def zeroPlus (W : ℝ → ℝ) (T : ℝ) : ℝ := sInf {x | 0 < x ∧ revMapBdry W T x = 0}

/-- The conformal welding homeomorphism induced by the reverse flow: `weldingHom W T x` is the
smallest `y ≥ 0` whose boundary image under `revMap W T` agrees with that of `x`. This is
genuinely a homeomorphism `[zeroMinus W T, 0] → [0, zeroPlus W T]` (Theorem 1.3) only in the
paper's setting, where `revHull W T` is a simple curve. -/
def weldingHom (W : ℝ → ℝ) (T : ℝ) (x : ℝ) : ℝ :=
  sInf {y | 0 ≤ y ∧ revMapBdry W T y = revMapBdry W T x}

end QuantumZipper

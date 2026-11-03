/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.SLE.Defs at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Loewner.Forward
import LatticeProb.Bonanno.QuantumZipper.Loewner.Reverse
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Chordal SLE: the driving function, and the random Loewner objects it drives

Chordal SLE_κ in `ℍ` from `0` to `∞` (Sheffield §1, following Schramm) is the random family
of centered forward/reverse Loewner flows of `QuantumZipper.Loewner.Forward` and
`QuantumZipper.Loewner.Reverse`, driven by the random function `W_t = √κ B_t`, where
`B` is a standard one-dimensional Brownian motion. This file packages that driving function
and the resulting trace, hulls, and maps as functions of `(κ, B, ω)`. See `FOUNDATIONS.md` §4.

Only the definitions are given here; that `B` is a.s. Brownian, and the probabilistic
properties of the resulting objects, are separate tasks.
-/

noncomputable section

open Filter
open scoped NNReal Topology

namespace QuantumZipper

variable {Ω : Type*}

/-- The sample path of `B` at `ω`, as a function of time alone: `pathOf B ω t = B t ω`. -/
def pathOf (B : ℝ≥0 → Ω → ℝ) : Ω → (ℝ≥0 → ℝ) := fun ω t => B t ω

/-- The SLE_κ driving function `W_t = √κ B_t` at sample point `ω`, extended to all `t : ℝ` by
using `t.toNNReal` (so `W_t = 0` for `t < 0`, which is never used). -/
def drive (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => Real.sqrt κ * B t.toNNReal ω

/-- The chordal SLE_κ trace driven by `B` at sample point `ω`: the forward-flow trace
`η(t) = lim_{y ↓ 0} f_t⁻¹(iy)` of `QuantumZipper.Loewner.Forward.trace`, driven by
`W = √κ B(·, ω)`. -/
def sleTrace (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℂ :=
  trace (drive κ B ω)

/-- The chordal SLE_κ hull at time `T`, driven by `B` at sample point `ω`: the points of `ℍ`
already swallowed by the forward flow driven by `W = √κ B(·, ω)`. -/
def sleHull (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ) : Set ℂ :=
  fwdHull (drive κ B ω) T

/-- The chordal SLE_κ forward Loewner map at time `T`, driven by `B` at sample point `ω`:
`z ↦ f_T(z)`, the centered forward flow of `QuantumZipper.Loewner.Forward.fwdMap` driven by
`W = √κ B(·, ω)`. -/
def sleFwdMap (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ) : ℂ → ℂ :=
  fwdMap (drive κ B ω) T

/-- The chordal SLE_κ reverse Loewner map at time `T`, driven by `B` at sample point `ω`:
`z ↦ u_T(z)`, the centered reverse flow of `QuantumZipper.Loewner.Reverse.revMap` driven by
`W = √κ B(·, ω)`, a conformal bijection `ℍ → ℍ \ sleRevHull κ B ω T`. -/
def sleRevMap (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ) : ℂ → ℂ :=
  revMap (drive κ B ω) T

/-- The chordal SLE_κ reverse hull at time `T`, driven by `B` at sample point `ω`: the part of
`ℍ` missed by the image of `sleRevMap κ B ω T`, of `QuantumZipper.Loewner.Reverse.revHull`
driven by `W = √κ B(·, ω)`. -/
def sleRevHull (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ) : Set ℂ :=
  revHull (drive κ B ω) T

/-- If the driving Brownian path vanishes at `0`, so does the driving function: `W_0 = 0`. -/
theorem drive_zero {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : B 0 ω = 0) :
    drive κ B ω 0 = 0 := by
  simp [drive, h]

/-- The driving function `drive κ B ω` is continuous whenever the sample path
`t ↦ B t ω` is continuous. -/
theorem drive_continuous {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : Continuous fun t : ℝ≥0 => B t ω) : Continuous (drive κ B ω) := by
  unfold drive
  exact continuous_const.mul (h.comp continuous_real_toNNReal)

end QuantumZipper

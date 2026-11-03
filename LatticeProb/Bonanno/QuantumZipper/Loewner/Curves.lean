/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Loewner.Curves at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Simple curves, chords, and their complementary components

Definitions of what it means for a hull-generating curve to be a simple arc in `ℍ` from a
real starting point (the case `κ < 4` of the reverse flow's hull, Sheffield §1.2–1.3), of a
chordal simple curve from `0` to `∞` in `ℍ` (the SLE trace itself), of the two complementary
components of `ℍ` cut off by such a chord, and of the normalized conformal uniformizer of a
component onto `ℍ`. See `FOUNDATIONS.md` §4.

Only the definitions are given here; the ODE-driven facts (that `revHull W T` is such a hull
when `κ < 4`, that the trace is such a chord, existence of the uniformizer via Riemann mapping
+ Carathéodory) are separate, later tasks.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace QuantumZipper

/-- `K` is the hull of a simple curve in `ℍ` started from a real point: there is a curve
`γ : [0,1] → ℂ`, continuous and injective on `[0,1]`, with `γ 0` real and `γ t ∈ ℍ` for all
`t ∈ (0,1]`, whose image on `(0,1]` is exactly `K`. This is the shape of `revHull W T` in the
paper's setting `κ < 4` (Sheffield §1.2), where the reverse flow's hull is cut off by a simple
arc from a boundary point. -/
def IsSimpleCurveHull (K : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 1) ∧ InjOn γ (Icc (0 : ℝ) 1) ∧
    (γ 0).im = 0 ∧ (∀ t ∈ Ioc (0 : ℝ) 1, γ t ∈ H) ∧ K = γ '' Ioc (0 : ℝ) 1

/-- `η` is a chordal simple curve from `0` to `∞` in `ℍ`: it starts at `0`, is continuous and
injective on `[0,∞)`, lies in `ℍ` for all positive times, and its norm tends to infinity. This
is the shape of the SLE trace `trace (drive κ B ω)` in the paper's setting `κ < 8`, where the
trace is a.s. a simple curve (Sheffield §1, Theorem 1.3 and its converse). -/
def IsSimpleChord (η : ℝ → ℂ) : Prop :=
  η 0 = 0 ∧ ContinuousOn η (Ici (0 : ℝ)) ∧ InjOn η (Ici (0 : ℝ)) ∧
    (∀ t > (0 : ℝ), η t ∈ H) ∧ Tendsto (fun t => ‖η t‖) atTop atTop

/-- The left complementary component of a chord `η`: the points of `ℍ \ η '' [0,∞)` that can
be joined, inside `ℍ \ η '' [0,∞)`, to some negative real point by a path whose only possible
escape from that set is at its own endpoint. For a simple chord `η`, this is one of the two
components `D₁, D₂` of `ℍ \ η` (Sheffield §1.2–1.3), namely the one adjacent to `(-∞,0)`. -/
def leftComponent (η : ℝ → ℂ) : Set ℂ :=
  {z | z ∈ (H \ η '' Ici (0 : ℝ)) ∧ ∃ x : ℝ, x < 0 ∧
    ∃ p : Path z (x : ℂ), ∀ t : unitInterval, t ≠ 1 → p t ∈ (H \ η '' Ici (0 : ℝ))}

/-- The right complementary component of a chord `η`: the points of `ℍ \ η '' [0,∞)` that can
be joined, inside `ℍ \ η '' [0,∞)`, to some positive real point by a path whose only possible
escape from that set is at its own endpoint. For a simple chord `η`, this is the other of the
two components `D₁, D₂` of `ℍ \ η` (Sheffield §1.2–1.3), the one adjacent to `(0,∞)`. -/
def rightComponent (η : ℝ → ℂ) : Set ℂ :=
  {z | z ∈ (H \ η '' Ici (0 : ℝ)) ∧ ∃ x : ℝ, 0 < x ∧
    ∃ p : Path z (x : ℂ), ∀ t : unitInterval, t ≠ 1 → p t ∈ (H \ η '' Ici (0 : ℝ))}

theorem leftComponent_subset_H (η : ℝ → ℂ) : leftComponent η ⊆ H :=
  fun _z hz => hz.1.1

theorem rightComponent_subset_H (η : ℝ → ℂ) : rightComponent η ⊆ H :=
  fun _z hz => hz.1.1

/-- `φ` is the normalized conformal uniformizer of `D` onto `ℍ`: a conformal (holomorphic and
bijective) bijection `D → ℍ` sending the marked boundary point `0` to `0` and `∞` to `∞`. In
the paper's setting `D` is one of the two components `D₁, D₂` cut off by the SLE trace, and
`φ` is unique up to `z ↦ a z` for `a > 0` (existence needs the Riemann mapping theorem plus
Carathéodory's extension theorem, a blueprint item). -/
def IsNormalizedUniformizer (D : Set ℂ) (φ : ℂ → ℂ) : Prop :=
  Set.BijOn φ D H ∧ DifferentiableOn ℂ φ D ∧ Tendsto φ (𝓝[D] 0) (𝓝 0) ∧
    Tendsto (fun z => ‖φ z‖) (Bornology.cobounded ℂ ⊓ 𝓟 D) atTop

/-- The normalized conformal uniformizer of `D` onto `ℍ`, chosen (via `Classical.epsilon`) to
satisfy `IsNormalizedUniformizer` when such a map exists, and junk otherwise. -/
def uniformizer (D : Set ℂ) : ℂ → ℂ :=
  Classical.epsilon (IsNormalizedUniformizer D)

end QuantumZipper

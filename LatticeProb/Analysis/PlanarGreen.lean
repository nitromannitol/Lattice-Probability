import Mathlib

/-!
# Planar Newtonian kernel, harmonic minorants and Green function of an open set

Definitions only; this module states and proves no theorem.

* `planarNewtonKernel`, `planarNewtonKernelEReal`: the logarithmic (Newtonian) kernel of the plane, with its
  extended-real version whose value at the pole is `+∞`.
* `IsHarmonicMinorant`, `greatestHarmonicMinorant`: harmonic minorants of an extended-real function on an open set,
  and their pointwise supremum.
* `greenFunction`: the Green function `G_O(x, y)` of an open set `O ⊆ ℂ`.

Convention. The Green function is normalized by `Δ G_O(x, ·) = -δ_x` and is the Newtonian kernel
`N(x, y) = -(2π)⁻¹ log ‖x - y‖` minus its greatest harmonic minorant on `O`:
`G_O(x, y) = N(x, y) - I_O[N(x, ·)](y)`. Source: Armitage and Gardiner, *Classical Potential Theory*
(Springer, 2001), Section 4.1; the normalization is that of Bou-Rabee and Gwynne, *Harmonic balls in Liouville
quantum gravity* (arXiv:2208.11795), Section 2.2 (Proposition 2.3).

Junk values. `greenFunction O x y : ℝ` takes the value `0` on the diagonal `x = y` (where the Green function is `+∞`)
and `0` if `x ∉ O` or `y ∉ O`. For an open set with no harmonic minorant of the kernel (for example `O = ℂ`) the
greatest harmonic minorant is `⊥` and the value of `greenFunction` is junk.
-/

namespace LatticeProb.Analysis

/-- The planar Newtonian (logarithmic) kernel `N(x, y) = -(2π)⁻¹ log ‖x - y‖`, the fundamental solution of `-Δ` on
`ℂ ≅ ℝ²`: `Δ N(x, ·) = -δ_x`. On the diagonal the true value is `+∞`; here `Real.log 0 = 0` gives the junk value
`0` (see `planarNewtonKernelEReal`). -/
noncomputable def planarNewtonKernel (x y : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Real.log ‖x - y‖

/-- The planar Newtonian kernel with pole `x` as an extended-real (superharmonic) function: `+∞` at `y = x` and
`planarNewtonKernel x y` elsewhere. Harmonic minorants are taken of this function, so the pole imposes no
constraint. -/
noncomputable def planarNewtonKernelEReal (x y : ℂ) : EReal :=
  if y = x then ⊤ else (planarNewtonKernel x y : EReal)

/-- `h` is a *harmonic minorant* of `u : ℂ → [-∞, ∞]` on `O`: `h` is harmonic on a neighbourhood of each point of
`O` and `h ≤ u` on `O` (Armitage and Gardiner, Section 4.1). -/
def IsHarmonicMinorant (O : Set ℂ) (u : ℂ → EReal) (h : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd h O ∧ ∀ y ∈ O, (h y : EReal) ≤ u y

/-- The *greatest harmonic minorant* `I_O[u]` of `u` on `O`, evaluated at `y`: the pointwise supremum of all harmonic
minorants of `u` on `O` (Armitage and Gardiner, Section 4.1). It is `⊥` where `u` has no harmonic minorant on `O`.
When `u` is superharmonic on the open set `O` and has a harmonic minorant there, `I_O[u]` is itself harmonic on `O`
and is the largest harmonic minorant; that is a theorem, not part of this definition. -/
noncomputable def greatestHarmonicMinorant (O : Set ℂ) (u : ℂ → EReal) (y : ℂ) : EReal :=
  ⨆ (h : ℂ → ℝ) (_ : IsHarmonicMinorant O u h), (h y : EReal)

open Classical in
/-- The *Green function* `G_O(x, y)` of an open set `O ⊆ ℂ`, normalized by `Δ G_O(x, ·) = -δ_x`: for `x, y ∈ O` with
`x ≠ y`, `G_O(x, y) = N(x, y) - I_O[N(x, ·)](y)`, where `N = planarNewtonKernel` and `I_O` is the greatest harmonic
minorant (Armitage and Gardiner, Section 4.1). Junk values: `0` on the diagonal `x = y`, and `0` if `x ∉ O` or
`y ∉ O`. -/
noncomputable def greenFunction (O : Set ℂ) (x y : ℂ) : ℝ :=
  if x ∈ O ∧ y ∈ O ∧ x ≠ y then
    planarNewtonKernel x y - (greatestHarmonicMinorant O (planarNewtonKernelEReal x) y).toReal
  else 0

end LatticeProb.Analysis

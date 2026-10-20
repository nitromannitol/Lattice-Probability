/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedWalk/Harmonic.lean.
-/
import LatticeProb.Network.Conductance
import Mathlib.Algebra.BigOperators.Fin

/-!
# Harmonicity on conductance graphs with possibly infinite degree

For a `ConductanceGraph` `G` and a function `h : V → ℝ`, `h` is harmonic at a vertex `x` when the
sum over the neighbours of `x` of the Laplacian terms `c(x,y) (h y - h x)` converges absolutely and
its total is zero. The absolute convergence is part of the definition: a vertex may have infinitely
many neighbours, and over a non-summable family `tsum` takes the junk value `0`, so the bare
vanishing of the sum would hold vacuously at such vertices.

The notions `IsHarmonicAt` and `IsHarmonicOn` live in the namespace `ConductanceGraph`. They are
different from LP's continuum harmonicity `LatticeProb.IsHarmonicOn`, and from the harmonicity
`netLaplacian G c h x = 0` of LP's finite networks in `LatticeProb.Network`. This file does not
relate them.

The examples at the end check that a constant function is harmonic on the path `0 – 1 – 2` with
unit conductances, and that the identity function is harmonic at its middle vertex.
-/

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- The neighbour sum of `c(x,y) |h y - h x|` converges, so the Laplacian sum at `x` converges
absolutely. -/
def AbsSummableAt (h : V → ℝ) (x : V) : Prop :=
  Summable fun y => G.c x y * |h y - h x|

/-- The summand of the discrete Laplacian at `x`; non-neighbours contribute `0`. -/
noncomputable def lapTerm (h : V → ℝ) (x : V) (y : V) : ℝ := G.c x y * (h y - h x)

/-- The absolute value of the Laplacian summand is `c(x,y) |h y - h x|`. -/
lemma abs_lapTerm (h : V → ℝ) (x y : V) :
    |G.lapTerm h x y| = G.c x y * |h y - h x| := by
  rw [lapTerm, abs_mul, abs_of_nonneg (G.c_nonneg x y)]

/-- `AbsSummableAt` is exactly absolute summability of the Laplacian summand. -/
lemma absSummableAt_iff (h : V → ℝ) (x : V) :
    G.AbsSummableAt h x ↔ Summable fun y => |G.lapTerm h x y| := by
  simp only [AbsSummableAt, G.abs_lapTerm]

/-- `h` is harmonic at `x`: the Laplacian sum at `x` converges absolutely and its total is zero. -/
def IsHarmonicAt (h : V → ℝ) (x : V) : Prop :=
  G.AbsSummableAt h x ∧ ∑' y, G.lapTerm h x y = 0

/-- `h` is harmonic at every vertex of a set. -/
def IsHarmonicOn (h : V → ℝ) (S : Set V) : Prop := ∀ x ∈ S, G.IsHarmonicAt h x

/-- Harmonicity at `x` includes the absolute convergence of the Laplacian sum. -/
lemma IsHarmonicAt.absSummable {h : V → ℝ} {x : V} (hx : G.IsHarmonicAt h x) :
    G.AbsSummableAt h x := hx.1

/-- Harmonicity at `x` includes the vanishing of the Laplacian sum. -/
lemma IsHarmonicAt.tsum_eq_zero {h : V → ℝ} {x : V} (hx : G.IsHarmonicAt h x) :
    ∑' y, G.lapTerm h x y = 0 := hx.2

end ConductanceGraph

/-! ## Examples

These show that the harmonicity notions are not vacuous on `ConductanceGraph.Example.path3`, the
path `0 – 1 – 2` with unit conductances. -/

namespace ConductanceGraph.Example

/-- A constant function is harmonic at every vertex of `path3`. -/
example (k : ℝ) : path3.IsHarmonicOn (fun _ => k) Set.univ := by
  intro x _
  simp [ConductanceGraph.IsHarmonicAt, ConductanceGraph.AbsSummableAt, ConductanceGraph.lapTerm]

/-- On `path3`, the identity function `x ↦ x` is harmonic at the middle vertex `1`. -/
example : path3.IsHarmonicAt (fun x : Fin 3 => ((x : ℕ) : ℝ)) 1 := by
  refine ⟨Summable.of_finite, ?_⟩
  norm_num [ConductanceGraph.lapTerm, path3, tsum_fintype, Fin.sum_univ_three]

end ConductanceGraph.Example

end LatticeProb.Network

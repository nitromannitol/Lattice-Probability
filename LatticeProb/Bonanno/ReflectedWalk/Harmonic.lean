/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.Harmonic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Energy

/-!
# Discrete harmonicity (Gwynne–Sung, Definition 1.2)

`h` is discrete harmonic at `x` when

  `∑_{y ∼ x} c(x,y) (h(y) − h(x)) = 0`.   (1.3)

**Footnote 2 of the paper is part of the definition.**  When `G` is not locally finite,
(1.3) implicitly requires the sum to converge absolutely, i.e.

  `∑_{y ∼ x} c(x,y) |h(y) − h(x)| < ∞`.

`IsHarmonicAt` therefore carries `AbsSummableAt` as a conjunct.  Do not replace it by the
bare vanishing of the `tsum`: over a non-summable family `tsum` is junk-valued `0`, so the
bare form would be satisfied vacuously at vertices where the defining sum diverges, and
would not formalize Definition 1.2.
-/

namespace ReflectedWalk

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- The absolute convergence required by footnote 2 of Gwynne–Sung. -/
def AbsSummableAt (h : V → ℝ) (x : V) : Prop :=
  Summable fun y => G.c x y * |h y - h x|

/-- The summand of the discrete Laplacian at `x`; non-neighbours contribute `0`. -/
noncomputable def lapTerm (h : V → ℝ) (x : V) (y : V) : ℝ := G.c x y * (h y - h x)

lemma abs_lapTerm (h : V → ℝ) (x y : V) :
    |G.lapTerm h x y| = G.c x y * |h y - h x| := by
  rw [lapTerm, abs_mul, abs_of_nonneg (G.c_nonneg x y)]

/-- `AbsSummableAt` is exactly absolute summability of the Laplacian summand. -/
lemma absSummableAt_iff (h : V → ℝ) (x : V) :
    G.AbsSummableAt h x ↔ Summable fun y => |G.lapTerm h x y| := by
  simp only [AbsSummableAt, G.abs_lapTerm]

/-- **Definition 1.2.**  `h` is discrete harmonic at `x`, including the absolute
convergence required by footnote 2. -/
def IsHarmonicAt (h : V → ℝ) (x : V) : Prop :=
  G.AbsSummableAt h x ∧ ∑' y, G.lapTerm h x y = 0

/-- `h` is discrete harmonic on a set of vertices. -/
def IsHarmonicOn (h : V → ℝ) (S : Set V) : Prop := ∀ x ∈ S, G.IsHarmonicAt h x

lemma IsHarmonicAt.absSummable {h : V → ℝ} {x : V} (hx : G.IsHarmonicAt h x) :
    G.AbsSummableAt h x := hx.1

lemma IsHarmonicAt.tsum_eq_zero {h : V → ℝ} {x : V} (hx : G.IsHarmonicAt h x) :
    ∑' y, G.lapTerm h x y = 0 := hx.2

end ConductanceGraph

end ReflectedWalk

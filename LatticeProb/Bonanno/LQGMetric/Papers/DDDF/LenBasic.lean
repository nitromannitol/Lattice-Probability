/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.LenBasic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LFPP
import LatticeProb.Bonanno.LQGDimension.LFPP.TreeInequalityAux
import Mathlib.Analysis.Complex.ReImTopology

/-!
# DDDF length observables, deterministic layer (task P2-DDDFLEN; blueprint DDDF.D2.len, S2.c)

DDDF = Ding–Dubédat–Dunlap–Falconet, *Tightness of Liouville first passage percolation for
γ ∈ (0,2)*, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.

DDDF (2.21) = `DefLength` (l. 457–460): `L^{(n)}_{a,b}(φ) := inf_π ∫_π e^{ξ φ_{0,n}} ds`, the
infimum over curves `π` in `R_{a,b} = [0,a] × [0,b]` joining its left and right sides; and
(l. 494–496) `L^{(n)}(P, φ)` for a rectangle `P` with two marked opposite sides. Here, for a
weight field `f : ℂ → ℝ`:

* `MarkedRect`: a closed rectangle `[x₀, x₀+w] × [y₀, y₀+h]` with marked sides (left/right if
  `horiz`, bottom/top otherwise); `rectAB a b` is DDDF's `R_{a,b}` with left/right marked.
* `crossLenIn ξ f U A B`: the infimum of `lfppLen ξ f P = ∫₀¹ e^{ξ f(P t)} |P'(t)| dt` over
  piecewise-C¹ paths `P` (FOUNDATIONS §7 `IsPiecewiseC1Path`) from `A` to `B` staying in `U`.
  (`Blueprint.lfppCrossIn ξ ε h` is `(crossLenIn ξ (h*_ε) [0,1]² leftSide rightSide).toReal`.)
  DDDF writes "smooth curves" (l. 462); we use piecewise-C¹ paths as DFGPS and GM do
  (blueprint DDDF.D2.len, proposed deviation D-DDDF-10).
* `rectLen ξ f R := crossLenIn ξ f R R.side₁ R.side₂` (= `L^{(n)}(P, φ)` with `f = φ_{0,n}`).

Results:
* `crossLenIn_le_of_abs_sub_le`: if `|f − g| ≤ c` on `U` then `L(f) ≤ e^{|ξ| c} L(g)`; this is
  DDDF's "straightforward" inequality `e^{−ξX_{a,b}} L(ψ) ≤ L(φ) ≤ e^{ξX_{a,b}} L(ψ)` (l. 482–485).
* `rectLen_ge`, `rectLen_le` (DDDF.S2.c, l. 908 "e^{−ξ‖φ_{0,n}‖} ≤ L^{(n)}_{1,1} ≤ e^{ξ‖φ_{0,n}‖}"):
  if `|f| ≤ M` on `R` then `e^{−|ξ|M} c ≤ L(R) ≤ e^{|ξ|M} c` with `c` the Euclidean crossing
  distance (`crossWidth`); the lower bound is "chord ≤ arclength", whose proof is ported from
  LQGDimension (`LQGDimension.TreeIneqJ42.chord_le_arclength`, `deriv_intervalIntegrable`,
  LFPP/TreeInequalityAux.lean l. 659–712), the upper bound is the straight segment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

namespace MarkedRect

end MarkedRect

/-- `P` is an admissible crossing path: piecewise C¹ from a point of `A` to a point of `B`,
staying in `U` -/
def AdmPath (U A B : Set ℂ) (P : ℝ → ℂ) : Prop :=
  ∃ z ∈ A, ∃ w ∈ B, IsPiecewiseC1Path P z w ∧ ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U

variable {ξ : ℝ} {f g : ℂ → ℝ} {U A B : Set ℂ}

/-! ### Comparison of weights -/

/-! ### Chord ≤ arclength (ported from LQGDimension) -/

/-! ### Crude bounds (DDDF.S2.c) -/

namespace MarkedRect

end MarkedRect

end DDDF
end LQGMetric

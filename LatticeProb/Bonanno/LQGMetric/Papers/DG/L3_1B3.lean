/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.L3_1B3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.L3_1B2

/-!
DG (`metric-comparison-final.tex`, Lemma 3.1 `lem-gff-compare`, DG:966–974; proof DG:2243–2244:
"Combine Lemmas 2.2, A.1, and A.2"), circle-average reading D100, `U = 𝕍`, `K` a box with
`B(z,1/10) ⊆ 𝕍`.

* `DGCircMod.neg` — the pair `(h², h¹)` from `(h¹, h²)`.
* `dg_lemma31_of_hU` — from the pair `(h, h^U)` (DG Lemma 2.2: `h − h^U = 𝔥` is harmonic with a
  Gaussian tail) and the proved pairs `(h^U, ĥ)`, `(h^U, ĥ^tr)`: the pairs `(h, ĥ)`, `(h, ĥ^tr)`.
* `DGLem31HCoupling` — **open input** (exact): a coupling of a white noise `W` and a normalized
  whole-plane GFF `h` for which the pair `(h, h^U)` (`h^U` the white-noise zero-boundary field on
  `𝕍`) satisfies `DGCircMod` on `K`. This is DG's "`h = h^U + 𝔥`" coupling with DG Lemma 2.2.
* **`dg_lemma31`** — DG Lemma 3.1 (all six pairs of `{h, h^U, ĥ, ĥ^tr}` on one probability space,
  `ĥ`, `ĥ^tr` from the same white noise) from `DGLem31HCoupling`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ GMCIdent GMCIdent2 GMCIdent3 SupTail QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the white-noise zero-boundary field `h^U` on `𝕍` tested against `σ_{z,r}` -/
def dgHU (W : WNSpace → Ω → ℝ) (z : ℂ) (r : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (measKerL2 openSquare (Ioi 0) (circleUnif z r)) ω

/-- `ĥ` tested against `σ_{z,r}` -/
def dgHat (W : WNSpace → Ω → ℝ) (z : ℂ) (r : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt Real.pi * W (hatMeasKerL2 (circleUnif z r)) ω

end DG
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L1Tr at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel

/-!
# DG's truncated white-noise field `ĥ^tr_t` and its spatial independence (task P2-DG3A)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, (3.4) (DG:916–918):
`ĥ^tr_t(z) := √π ∫_{t²}^1 ∫_ℂ p_{B_{1/10}(z)}(s/2; z, w) W(dw, ds)`, `t ∈ (0,1]`, and the key
property (DG:923–925): "if `A, B ⊂ ℂ` with `dist(A,B) ≥ 1/5`, then `{ĥ^tr_t|_A}` and
`{ĥ^tr_t|_B}` are independent. Indeed, this is because [they] are determined by the restrictions
of the white noise `W` to the disjoint sets `B_{1/10}(A) × ℝ₊` and `B_{1/10}(B) × ℝ₊`."

* `hatTr W t z` — DG's `ĥ^tr_t(z)` (pointwise field, `t > 0`), with kernel
  `1_{[t²,1]}(s) p_{B_{1/10}(z)}(s/2; z, w)`, i.e. DZZ's white-noise kernel
  `DZZ.wndKernelL2 (B_{1/10}(z)) [t², 1] z` (killed heat kernel `KilledHeat.killedHeat`);
* `supportedIn_hatTrKernel` — the kernel vanishes off `ℝ × B_{1/10}(z)`;
* `indepFun_hatTr` — **DG's spatial independence**, by DG's argument: the two families are
  functions of the white noise restricted to the disjoint sets `ℝ × B_{1/10}(A)`,
  `ℝ × B_{1/10}(B)` (`WhiteNoise.IsWhiteNoise.indepFun_of_disjoint`).

DG Lemma 3.1 (the coupling with `h`, `h^U`, `ĥ` and the Gaussian tails of the differences,
App. A) is not formalized here; see `handoff/P2-DG3A.md`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DG

open KilledHeat WhiteNoise DZZ

/-- the kernel of `ĥ^tr_t(z)`: `(s, w) ↦ 1_{[t²,1]}(s) p_{B_{1/10}(z)}(s/2; z, w)` in `L²` -/
def hatTrKernel (t : ℝ) (z : ℂ) : WNSpace :=
  wndKernelL2 (Metric.ball z (1 / 10)) (Icc (t ^ 2) 1) z

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end DG
end LQGMetric

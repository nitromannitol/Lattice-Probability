/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53FN2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53FN1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF3

/-!
# DZZ Lemma 5.3 part 1, final assembly 2: the node-4 bad events at `ε = ε*²` (P2-DZZ53FIN)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522. On the selected chain
(AUDIT-2026-10-03-N, N6 (ii)) the interface bound is `μH¹(Λ₁) ≥ ε*² s_b` (G-A1, N12), so Markov's
threshold is `0.01 ε*² s_b`, the cut-off is `ε*² s_b/1600` (N7) and the proxy must be fine enough
for the coupling (`2^{-m_b} ≤ ε*² s_b/(1600 |v−u|)`).

* `l53fnM`: the node-4 proxy of the box `b`, as `l53ufM` (S5L53UF3) with the level
  `m_b = n_b + 2 n_{ε*} + 12` (so `2^{-m_b} = ε*² s_b/4096`).
* **`l53fn_hbad`**: `P(bad_w at boxAt n w) ≤ (800/ε*²) · 2K⁻⁴` (copy of `l53uf_hbad`, S5L53UF3,
  with `ε*` replaced by `ε*²`; it uses `l53WBadQ_le_cut`, S5L53UF2, and `l53uf_far_bound`,
  S5L53UF1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The node-4 proxy of the box `b`** at `δ = 2^{-k}` on the selected-chain route
(level `n_b + 2 n_{ε*} + 12`). -/
def l53fnM (W : WNSpace → Ω → ℝ) (γ αs : ℝ) (k : ℕ) (b : DyBox) :
    Ω → ℚ × ℚ → ℚ → ℝ≥0∞ :=
  proxyMass W γ (b.n + 2 * epsStarN αs ((2 : ℝ)⁻¹ ^ k) + 12)
    (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k / b.side *
      Real.exp (((k : ℝ) * Real.log 2) ^ (0.91 : ℝ) / 2)) ^ 2))
    (sqBox b.center (5 * b.side))

variable {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end DZZ
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53M3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53M2

/-!
# DZZ Lemma 5.3, part 1, node 4: the union bound over the cells of `u` and `v` (P2-DZZ53M)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522.

* `l53_head_iface`, `l53_last_iface`: `Λ₁ ⊆ ∂𝖢₁` and `Λ_{d−1} ⊆ ∂𝖢_d`, with
  (eq-Lambda-i-not-small) `μH¹(Λ) ≥ ε s` for the cell of `u` resp. `v`.
* **`l53UVBadR_le`**: node 4. With local proxies `νP b` for the candidate cells
  `b = boxAt n w` (`w ∈ {u, v}`, `n ≤ N`) having the per-point far bound `p` on `∂b`, and a
  good event `G` (`P Gᶜ ≤ q`) on which `μ0 ≤ νP b` on the balls of `𝕍_{c_b, 5s_b}` whenever
  `b` is a cell containing `u` or `v`:
  `P(l53UVBadR) ≤ q + 2(N+1)(400/ε*) p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma l53_getD_eq (c : List DyBox) {i : ℕ} (hi : i < c.length) : c.getD i DyBox.root = c[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

variable {Ω : Type*} [MeasurableSpace Ω]

end DZZ
end LQGMetric

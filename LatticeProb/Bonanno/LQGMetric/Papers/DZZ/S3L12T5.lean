/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12T5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12T4

/-!
# DZZ Lemma 3.12, one-step claim: reduction to the choice of the replacing segment (P2-DZZ312S)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1478–1497 (Cases 1–3): the replacing
segment `𝒞_{i,replace}` consists of cells of side `≥ ε* s_𝖢` meeting `𝖢_large` (cells of
`𝒞_{i,cross}`, or `𝖢`), and `ψ(𝒞_{i,replace})` has at most one cell (Case 1: none; Case 2:
`𝖢_{i,1}`; Case 3: none). This file derives `L312Replace` from exactly that:

* `side_gt_of_mem_l312Bad`: in a sequence of cells of side `≥ ε s`, bad cells have side `> s`;
* `two_mul_side_le_of_lt`: dyadic sides: `s_c > s_𝖢 ⇒ s_c ≥ 2 s_𝖢`;
* `L312Core` (open): DZZ's choice of `𝖢_{i,1}`, `𝖢_{i,2}`, `𝒞_{i,replace}` (l. 1462–1497);
* **`l312Replace_of_core : L312Core γ → L312Replace γ`** (length by `length_le_of_near`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

lemma side_gt_of_mem_l312Bad {ε s : ℝ} (hε : 0 < ε) {W : List DyBox}
    (hW : ∀ c ∈ W, ε * s ≤ c.side) {c : DyBox} (hc : c ∈ l312Bad ε W) : s < c.side := by
  obtain ⟨-, c', hp, hs⟩ := exists_pair_of_mem_l312Bad hc
  have hc' : c' ∈ W := by
    rcases hp with h | h
    · exact infix_mem_right h
    · exact infix_mem_left h
  have := hW c' hc'
  by_contra h; push Not at h
  have : ε * c.side ≤ ε * s := mul_le_mul_of_nonneg_left h hε.le
  linarith

lemma two_mul_side_le_of_lt {c C : DyBox} (h : C.side < c.side) : 2 * C.side ≤ c.side := by
  have hn : c.n < C.n := by
    by_contra hn; push Not at hn
    have : c.side ≤ C.side := by
      unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    linarith
  unfold DyBox.side
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hn
  rw [hd, pow_add, pow_add, pow_one]
  have h0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ c.n := by positivity
  have h1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

end DZZ
end LQGMetric

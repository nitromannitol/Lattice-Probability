/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12S6 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S5

/-!
# DZZ Lemma 3.12, one-step claim: chains of cells as continuous paths (P2-DZZ316)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1443–1447 (`𝒞_i` "has to enter from
outside and exit from `∂𝖢_large`"; `𝖢_enter`, `𝖢_exit`) and l. 1468–1470 (`𝒞_{i,cross}` intersects
`[𝖢_enter, 𝖢_exit]`): to use the enclosure (`EnclosesBox`, continuous paths, decision D84) a
sequence of neighbouring boxes is turned into a continuous path through their closures. Own
elementary arguments.

* `convex_closedBox`;
* **`exists_path_of_chain`**: a chain of boxes (consecutive ones equal or neighbours) carries a
  continuous path from any point of the first box to any point of the last, inside the union of
  the closed boxes;
* **`exists_mem_frontier_of_chain`**: such a chain from a point outside `S` to a point of `S` has
  a box meeting `∂S`;
* **`exists_meet_of_enclosesBox`**: a chain from `𝖢` to `∂𝖢_large` meets every enclosure of `𝖢`
  (closed boxes intersect);
* **`exists_enter_of_bad`**: existence of `𝖢_enter` (a cell before the bad cell `𝖢` meeting
  `∂𝖢_large`); `𝖢_exit` is symmetric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

lemma comb_ge {lo p q a c : ℝ} (hp : lo ≤ p) (hq : lo ≤ q) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a + c = 1) : lo ≤ a * p + c * q := by
  have e : lo = a * lo + c * lo := by rw [← add_mul, hac, one_mul]
  rw [e]; exact add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hc)

lemma comb_le {hi p q a c : ℝ} (hp : p ≤ hi) (hq : q ≤ hi) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a + c = 1) : a * p + c * q ≤ hi := by
  have e : hi = a * hi + c * hi := by rw [← add_mul, hac, one_mul]
  rw [e]; exact add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hc)

lemma convex_closedBox (b : DyBox) : Convex ℝ b.closedBox := by
  intro x hx y hy a c ha hc hac
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  have r : (a • x + c • y).re = a * x.re + c * y.re := by simp
  have i : (a • x + c • y).im = a * x.im + c * y.im := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r]; exact comb_ge x1 y1 ha hc hac
  · rw [r]; exact comb_le x2 y2 ha hc hac
  · rw [i]; exact comb_ge x3 y3 ha hc hac
  · rw [i]; exact comb_le x4 y4 ha hc hac

variable {m : DyBox → ℝ} {δ : ℝ}

end DZZ
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58P5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58P4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Paths
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Fin2

/-!
# GM Lemma 5.8: the Euclidean paths of Step 2 (task P2-M2L58c)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Steps 1–2 (l. 3068–3091). The points of `L58Paths`: two windows of `n` points on the upper
half of `∂B_r(0)` (real parts `−r/4 + 10Rj` and `r/8 + 10Rj`, `R = δr/(500n)`), `A` = the two
windows. Their angular bands are disjoint, so `x` avoids one of them (`good_window`); that window
carries the paths of `window_paths` (`Geom58T3`); assembled in `l58Paths` (`Geom58T4`). Own explicit
construction (GM leave the points and the paths
implicit, l. 3069–3086); GM's `𝒵` has `#A · δ ≤ 100` arcs, here `#A ≤ 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM

lemma card_win {r R c : ℝ} (hR : 0 < R) (n : ℕ) :
    ((Finset.range n).image (winPt r R c)).card = n := by
  rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro j j' h
  have h' := congrArg Complex.re h
  rw [winPt_re, winPt_re] at h'
  have : (j : ℝ) = j' := by
    have h10 : (10 * R) * (j : ℝ) = (10 * R) * j' := by linarith
    exact mul_left_cancel₀ (by positivity) h10
  exact_mod_cast this

lemma mem_win {r R c : ℝ} {n : ℕ} {z : ℂ} (hz : z ∈ (Finset.range n).image (winPt r R c)) :
    ∃ j < n, z = winPt r R c j := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
  exact ⟨j, Finset.mem_range.1 hj, rfl⟩

end LQGMetric.GM

/-
The return time of a path after its first hit of a negative level.

For a level `c > 0`, `upcrossReturn c v` is the first time the path `v` returns to `0` after its
first hit of `-c`.  For a continuous path starting at `0`, the first hit of `-c` is strictly
positive (`zero_lt_hitFrom_neg`), and it is never later than the return time
(`hitFrom_neg_le_upcrossReturn`).
-/
import LatticeProb.Prob.UpcrossShift
import LatticeProb.Prob.UpcrossMeasurable

open Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- A continuous path starting at `0` needs positive time to reach the level `-c < 0`. -/
theorem zero_lt_hitFrom_neg {v : ℝ≥0 → ℝ} {c : ℝ} (hv : Continuous v) (hv0 : v 0 = 0)
    (hc : 0 < c) : 0 < hitFrom (-c) 0 v := by
  by_cases h : hitFrom (-c) 0 v = ⊤
  · rw [h]
    exact ENNReal.zero_lt_top
  · obtain ⟨s, hs, -, hvs, -⟩ := exists_hitFrom_eq hv h
    rw [hs]
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [hv0] at hvs
      linarith
    exact ENNReal.coe_pos.2 (pos_iff_ne_zero.2 hs0)

/-- The first hit of `-c` is never later than the return to `0` after it. -/
theorem hitFrom_neg_le_upcrossReturn (c : ℝ) (v : ℝ≥0 → ℝ) :
    hitFrom (-c) 0 v ≤ upcrossReturn c v :=
  le_hitFrom

end LatticeProb

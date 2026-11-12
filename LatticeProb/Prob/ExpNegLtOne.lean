import Mathlib
import LatticeProb.Prob.UpcrossLaplace

/-!
# `e^{-q r} < 1` for positive `q` and positive `r`

`LatticeProb.expNeg_lt_one`: for `q > 0` and `r ∈ (0, ∞]` the Laplace weight `e^{-q r}` is `< 1`
(for `r = ∞` it is `0`).
-/

open scoped ENNReal

noncomputable section

namespace LatticeProb

/-- For `q > 0` and `r > 0`, `e^{-q r} < 1` (with `e^{-q ∞} = 0`). -/
lemma expNeg_lt_one {q : ℝ} (hq : 0 < q) {r : ℝ≥0∞} (hr : 0 < r) : expNeg q r < 1 := by
  by_cases h : r = ⊤
  · simp [h]
  · have hpos : 0 < r.toReal := ENNReal.toReal_pos hr.ne' h
    simp only [expNeg, h, ↓reduceIte]
    refine ENNReal.ofReal_lt_one.2 ?_
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by nlinarith)

end LatticeProb

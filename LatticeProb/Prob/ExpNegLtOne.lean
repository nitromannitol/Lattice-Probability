import Mathlib
import LatticeProb.Prob.UpcrossReturnLaplace

/-!
# `e^{-q r} < 1` for positive `q` and positive `r`

The lemma `LatticeProb.expNeg_lt_one {q : ℝ} (hq : 0 < q) {r : ℝ≥0∞} (hr : 0 < r) : expNeg q r < 1`
(`e^{-q r} < 1`, with `e^{-q ∞} = 0`) is proved in `LatticeProb.Prob.UpcrossReturnLaplace`.
This module only re-exports it, so that `import LatticeProb.Prob.ExpNegLtOne` provides it.
-/

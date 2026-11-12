/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6TailsDec at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Sup
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698Main
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# DDDF (6.102)/(6.103): decoupling the low frequencies (task P2-DDDF6c)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1608–1613 and 1639–1647 ("using the same argument
as in [(6.98)]"): for `δ = 2^{-(n+r)}`, `φ_{δ,1} = φ_{2^{-r},1} + φ_{δ,2^{-r}}`, the first has a
Gaussian sup tail uniformly in `r` (`S6.low_sup_tail_quant`), and
`L(φ_{δ,2^{-r}}) =ᵈ 2^{-r} L^{(n)}_{2^r,2^r}` (`S6.law_hi`). `S6.tail_decomp` bounds both tails of
`L^{(δ)}_{1,1}` by the Gaussian tail plus the tails of `2^{-r} L^{(n)}_{2^r,2^r}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DDDF
namespace S6

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} {ξ : ℝ}

/-- `δ ∈ (0,1)` is `2^{-(n+r)}` with `n ∈ ℕ`, `r ∈ [0,1]` -/
lemma exists_split {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    ∃ (n : ℕ) (r : ℝ), 0 ≤ r ∧ r ≤ 1 ∧ δ = (2 : ℝ) ^ (-((n : ℝ) + r)) := by
  set x := -Real.logb 2 δ
  have hx : 0 ≤ x := by
    have : Real.logb 2 δ < 0 := Real.logb_neg (by norm_num) h0 h1
    linarith
  refine ⟨⌊x⌋₊, x - ⌊x⌋₊, by linarith [Nat.floor_le hx], by
    linarith [Nat.lt_floor_add_one x], ?_⟩
  rw [show (⌊x⌋₊ : ℝ) + (x - ⌊x⌋₊) = x by ring, neg_neg, Real.rpow_logb (by norm_num)
    (by norm_num) h0]

end S6
end DDDF
end LQGMetric

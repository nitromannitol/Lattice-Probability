/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P317B at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317A

/-!
# DZZ Proposition 3.17 from Proposition 3.2, the crude moments and the concentration of `D'`
(P2-DZZ32G)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1526–1530, 1627–1630): "It is obvious from
Proposition 3.2 and Corollary 3.3 that (eq-concentration-1) is equivalent to … (eq-concentration-
approximate)", and the same for (eq-concentration-2). Here the "obvious" direction:
`|X - E X| ≤ |X - Y| + |Y - E Y| + |E Y - E X|` with `X = log min D`, `Y = log D'`;
`|X - Y| ≤ (log δ⁻¹)^{0.9}` on the event of Prop 3.2, and `|E X - E Y| ≤ K'(log δ⁻¹)^{0.9}`
(the Cor 3.3 step `abs_integral_sub_le_of_highProb`, for the admissible pair).

* **`dzzProp317_of_approx`**: `DZZProp32U P γ W μ ξ ξ → DZZCrudeMoments P γ W μ ξ →
  DZZConcApprox P γ W ξ → DZZProp317 P μ ξ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the triangle step: `|X - E X| ≤ |X - Y| + |Y - E Y| + |E Y - E X|` -/
lemma abs_sub_int_le {x y ex ey a b e : ℝ} (h1 : |x - y| ≤ a) (h2 : |y - ey| ≤ b)
    (h3 : |ex - ey| ≤ e) : |x - ex| ≤ a + b + e := by
  have := abs_sub_le x y ex
  have := abs_sub_le y ey ex
  rw [abs_sub_comm ey ex] at this
  linarith

end DZZ
end LQGMetric

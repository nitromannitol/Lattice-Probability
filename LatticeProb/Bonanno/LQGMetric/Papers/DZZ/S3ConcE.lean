/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcE at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcD

/-!
# (eq-concentration-approximate-2) and `DZZConcApprox` (P2-DZZCONC)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 1640–1651: with `ℓ_δ = (log δ⁻¹)^{0.9}`,
`P(𝒳_δ ∉ 𝒜) ≤ δ^a`, the Gaussian bound `e^{−Ω((log δ⁻¹)^{0.8})}` (l. 1647), and the
mean–median step with `M = (log δ⁻¹)^{1.1}` (higher powers absorbing lower ones, l. 1626).

* `dzzConcApprox2_of`: (eq-concentration-approximate-2) from `DZZDistLip2`.
* **`dzzConcApprox_of`**: `DZZDistLip1 → DZZDistLip2 → DZZCrudeMoments → DZZConcApprox`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

/-- `L^x L^y = L^{x+y}` for `L > 0` -/
lemma rpow_mul_rpow' {L : ℝ} (hL : 0 < L) (x y : ℝ) : L ^ x * L ^ y = L ^ (x + y) :=
  (Real.rpow_add hL x y).symm

end DZZ
end LQGMetric

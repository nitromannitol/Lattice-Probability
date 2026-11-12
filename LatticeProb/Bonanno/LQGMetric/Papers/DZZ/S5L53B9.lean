/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32X

/-!
# DZZ Lemma 3.8 for the walled (tilde) distances, with the comparison only on the wall's box
(P2-DZZ53b)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Lemma 3.8 (`lem-LGD-compare`, l. 1218–1233) assumes
(eq-var-compare) and (eq-coupling-two-fields) on all of `𝕍`. For the tilde distance
`D̃ = D^{𝕍̃_{u,v}}` (balls contained in `𝕍̃_{u,v}`, DZZ l. 2277–2279) only the field inside the box
matters; DZZ Remark 5.2 (l. 2283–2286) and l. 2318–2322 ("Applying Lemma 2.9 to each pair
`(𝕍̃_{ū,v̄}, 𝕍̃_{y_i,y_{i+1}})` … as well as using Lemma 3.8") use Lemma 3.8 in this localized form,
for the walled measures `dzzWall K μᵢ`, with the comparison assumed only on `𝕍 ∩ K`.
The proof is DZZ's (l. 1229–1232); a ball not contained in `K` up to a Lebesgue-null set has
infinite walled mass.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

lemma dzzWall_apply_ball (K : Set ℂ) (μ : Measure ℂ) (z : ℂ) (r : ℝ) :
    dzzWall K μ (Metric.ball z r) = μ (Metric.ball z r) + ⊤ * volume (Metric.ball z r ∩ Kᶜ) := by
  simp only [dzzWall, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply Metric.isOpen_ball.measurableSet]

end DZZ
end LQGMetric

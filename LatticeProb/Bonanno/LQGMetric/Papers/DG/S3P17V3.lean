/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17V3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17V1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17L1
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17 at `𝕍`-scale, part 3: the lower bound of Step 3 carried to `𝕊` (P2-DG317V)

Ding–Gwynne arXiv:1807.01072 (`metric-comparison-final.tex`), proof of Prop 3.17, Step 3
(DG:1587–1589), D121. The lower bound `D^ε(K', ∂U') ≥ ε^{-1/(d+ζ)}` (`DGP317Lb`, the input of
`dgP317Show_of`/`p17s_good`) for `μ' = (T⁻¹)_* μ` on `[−1/6,7/6]²` follows from P2-DGLB's
`dgP317Lb_of` (DG Lemmas 3.21 + 3.5, from `DGLem319Scaled P W' μ` on `[1/12,11/12]²`, the form
taken by `dg_prop322_sqOne_muHat`) at `𝕍`-scale for `T(K') ⊆ [1/4,3/4]²`: the LGD only
increases under `T⁻¹` (`p17v_lgd_up`) and `T` halves distances. Own elementary glue
(DV-DG317V-1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma p17v_pre_pre (S : Set ℂ) : p17vT ⁻¹' (p17vTinv ⁻¹' S) = S := by
  ext z; simp [p17vTinv_T]

end DG
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3CM9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CM8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P317B

/-!
# DZZ Proposition 3.17 at `μIn` from the concentration of `D′` (D122)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.17 (l. 1519–1652) at the measure `μIn`:
Prop 3.2 at `μIn` (`dzz_prop32U_dzzMuIn`, S3P32G6), the small-`δ` crude moments
(`dzzCrudeMomentsEv_dzzMuIn`, S3CM8; D122) and the concentration of the approximate distance
(`DZZConcApprox`, l. 1528–1530, 1628–1630) give `DZZProp317` through `dzzProp317_of_approxEv`.
(Composition proposed by P2-DZZCM; possible since S3P32Z2's `exists_grid_near` was renamed
`p32z_exists_grid_near`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **DZZ Proposition 3.17 at `μIn`**, modulo the concentration of `D′` (`DZZConcApprox`) -/
theorem dzzProp317_dzzMuIn_ofConc {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) (hconc : DZZConcApprox P γ W ξ) :
    DZZProp317 P (dzzMuIn γ W) ξ := by
  have := hW.isProbabilityMeasure
  exact dzzProp317_of_approxEv (dzz_prop32U_dzzMuIn hW hγ hγ2 hξ hξc)
    (dzzCrudeMomentsEv_dzzMuIn hW hγ hγ2 hξ) hconc

end DZZ
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32G6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32F4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32G5

/-!
# DZZ Proposition 3.2 and Corollary 3.3 at `μIn`, unconditional (P2-DZZ32G)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`), Prop 3.2 (`prop-approximate-LGD`, l. 807–812, proof
l. 1087–1207) and Cor 3.3 (`cor-approximate-LGD-expectation`, l. 859–862) at the walled measure
`μIn = dzzMuIn γ W` (D102):

* **`dzz_prop32U_dzzMuIn`**: `DZZProp32U P γ W μIn ξ ξd` (both halves: lower half
  `l32BallCover_dzzMuIn_eta`, upper half from `l32EncPhiHPW_dzzMuIn` and the proved start cover
  `l32StartPhiHPC_dzzMuIn`);
* `dzzProp32_of_U`: the adapter `DZZProp32U → DZZProp32` (pairs admissible at every `δ ∈ (0,1)`,
  `IsXiAdmissibleSeq`, are admissible at each `δ`, `IsXiAdmissibleAt`);
* **`dzz_prop32_dzzMuIn`**: `DZZProp32 P γ W μIn ξ ξd` (DZZ's statement for `ξd = ξ`);
* **`dzz_cor33_dzzMuIn`**: DZZ Cor 3.3 at `μIn` (rate `(log δ⁻¹)^{-0.1}`, as `dzz_cor33`), from
  the crude moment bounds (eq-very-crude), (eq-very-crude-prime) (l. 849–857) as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

/-- **DZZ Prop 3.2 at `μIn`** (uniform form, D71), unconditional. -/
theorem dzz_prop32U_dzzMuIn {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) :
    DZZProp32U P γ W (dzzMuIn γ W) ξ ξd :=
  dzz_prop32U_dzzMuIn_of hW hγ hγ2 hξ hξd (isClipDepth_rP32 γ) (l32EncPhiHPW_dzzMuIn hW hγ hγ2)
    (l32StartPhiHPC_dzzMuIn hW hγ hγ2)

end DZZ
end LQGMetric

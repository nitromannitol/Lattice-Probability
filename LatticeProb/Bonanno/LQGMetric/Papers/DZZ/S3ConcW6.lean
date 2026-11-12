/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcW6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcW5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3CMW3

/-!
# Walled DZZ Proposition 3.17 at a dyadic wall from the walled (Eq.boundDprime) (P2-DZZCONCW)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.17 (l. 1505–1517, proof l. 1519–1652) for the
walled LGD `D^{B̄}` and `D'_{cellsInside B}` (Remark 5.2, l. 2281–2284; D117, D123).

* **`dzzConcApproxOn_inside`**: `DZZConcApproxOn P γ W B̄ (cellsInside B) ξ` (walled
  (eq-concentration-approximate), (eq-concentration-approximate-2)) from the walled
  (Eq.boundDprime) `L32UpperCrossInside γ B ξ` only: the walled `𝓔*` (S3ConcW1–W2), the walled
  good sets (S3ConcW3), the Lipschitz data (S3ConcW4), the regularity of `𝒳_δ` (`dzzCoarseReg`,
  S3ConcK), the walled crude moments (`dzzCrudeMomentsEvOn_inside`, S3CMW3) and the Gaussian
  concentration (S3ConcW5);
* **`dzzProp317In_dzzMuIn_inside`**: `DZZProp317In P (dzzWall B̄ μIn) B̄ ξ` from
  `L32UpperCrossInside γ B ξ` only, through `dzzProp317In_dzzMuIn_inside_of` (S3P317E) and the
  proved walled L3.5 `dzz_lemma35UOn_wall` (S3L5W8).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

universe u

/-- **Walled (eq-concentration-approximate), (eq-concentration-approximate-2) at a dyadic wall**
(DZZ l. 1528–1530, 1628–1630, proof l. 1538–1651, for `D'_{cellsInside B}`). -/
theorem dzzConcApproxOn_inside {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (B : DyBox) {ξ : ℝ} (hξ : 0 < ξ) (hξc : ξ < dzzCMc γ) (hX : L32UpperCrossInside γ B ξ) :
    DZZConcApproxOn P γ W B.closedBox (cellsInside B) ξ := by
  have := hW.isProbabilityMeasure
  exact dzzConcApprox_ofEvIn
    (dzzDistLip1In_of_core hW hγ hγ2 (dzzCoarseReg hW γ)
      (dzzDistLip1CoreIn_of hW hγ hγ2 B hξ hξc hX))
    (dzzDistLip2In_of_core hW hγ hγ2 (dzzCoarseReg hW γ)
      (dzzDistLip2CoreIn_of hW hγ hγ2 B hξ hξc hX))
    (dzzCrudeMomentsEvOn_inside hW hγ hγ2 B hξ)

end DZZ
end LQGMetric

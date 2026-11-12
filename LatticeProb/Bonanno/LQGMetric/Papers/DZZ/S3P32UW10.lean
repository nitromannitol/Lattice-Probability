/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW10 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW9
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcW2

/-!
# Walled (Eq.boundDprime) at a dyadic wall, unconditional (P2-DZZUPW, packet P-317K-UP)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.2, (Eq.boundDprime) l. 1088–1103, with
Remark 5.2 (l. 2281–2284), for `K = B̄`, `S = cellsInside B`, `μ = dzzWall B̄ μIn`:

* **`l32UpperCrossOn_dzzMuIn`**: `L32UpperCrossOn P γ W B̄ (cellsInside B) (dzzWall B̄ μIn) ξ ξd`
  for every white noise, `0 < ξ`, `ξd < C_Mc` — from `l32UpperCrossOn_of` (S3P32UW3) and the two
  walled inputs `l32EncPhiHPWOn_dzzMuIn` (S3P32UW7), `l32StartPhiHPCOn_dzzMuIn` (S3P32UW9) at the
  clipping depth `rP32 γ`;
* **`l32UpperCrossInside_holds`**: the hypothesis `L32UpperCrossInside γ B ξ` of the walled
  P3.17 (`dzzProp317In_dzzMuIn_inside`, S3ConcW6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **Walled (Eq.boundDprime) at a dyadic wall** (DZZ l. 1088–1103 + Remark 5.2). -/
theorem l32UpperCrossOn_dzzMuIn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (B : DyBox) {ξ ξd : ℝ} (hξ : 0 < ξ) (hξd : ξd < dzzCMc γ) :
    L32UpperCrossOn P γ W B.closedBox (cellsInside B)
      (fun ω => dzzWall B.closedBox (dzzMuIn γ W ω)) ξ ξd :=
  l32UpperCrossOn_of hW hγ hγ2 (isClipDepth_rP32 γ) B (l32EncPhiHPWOn_dzzMuIn hW hγ hγ2 B)
    (l32StartPhiHPCOn_dzzMuIn hW hγ hγ2 B) hξ hξd

/-- The walled upper crossing for every white noise and every `ξd < C_Mc`, in the form consumed by
`dzzProp317In_dzzMuIn_inside` (S3ConcW6). -/
theorem l32UpperCrossInside_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (B : DyBox) {ξ : ℝ}
    (hξ : 0 < ξ) : L32UpperCrossInside γ B ξ :=
  fun hW _ hξd => l32UpperCrossOn_dzzMuIn hW hγ hγ2 B hξ hξd

end DZZ
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5WallSim6E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6D
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW10
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5InputsW1

/-!
# P-317K-SIM, part 6E: the walled P3.17 at the walls, unconditionally

`dzzProp317Walls_dzzMuIn_of` (S5WallSim6D) with the walled (Eq.boundDprime)
`l32UpperCrossInside_holds` (S3P32UW10, P2-DZZUPW): **`dzzProp317Walls_dzzMuIn`**, and the
packaged leaf `DZZInW.DZZProp317WallsAll` (S5InputsW1) with `ξ₂ = min (1/80) (C_Mc/2)`:
**`dzzProp317WallsAll_holds`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- **Walled DZZ Proposition 3.17 at every wall of the DG chain** (DZZ l. 1505–1517, Remark 5.2,
l. 2281–2284) for `0 < ξ ≤ 1/80`, `2ξ < C_Mc`. -/
theorem dzzProp317Walls_dzzMuIn {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80) (h2ξ : 2 * ξ < dzzCMc γ) :
    DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls :=
  dzzProp317Walls_dzzMuIn_of hW hγ hγ2 hξ hξ1 h2ξ (l32UpperCrossInside_holds hγ hγ2 wsimB₀ hξ)

/-- **The leaf `DZZProp317WallsAll`** of P2-CONFW. -/
theorem dzzProp317WallsAll_holds : DZZInW.DZZProp317WallsAll := by
  intro Ω _ P W hW γ hγ hγ2
  refine ⟨min (1 / 80) (dzzCMc γ / 2), lt_min (by norm_num) (by have := dzzCMc_pos γ; linarith),
    fun ξ hξ hξ2 => dzzProp317Walls_dzzMuIn hW hγ hγ2 hξ
      ((hξ2.trans_le (min_le_left _ _)).le) ?_⟩
  have := hξ2.trans_le (min_le_right _ _)
  linarith

end DZZ
end LQGMetric

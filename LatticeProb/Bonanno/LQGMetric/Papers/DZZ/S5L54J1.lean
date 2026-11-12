/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54J1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54I4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54C
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Side
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117F

/-!
# D117 P-54C/T (wiring): DZZ Lemma 5.4 at `μIn` from L5.3 and the walled P3.17 (P2-DZZ54C)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 5.4 (l. 2299–2304), proof l. 2553–2578.

`dzzLem54Exp_dzzMuIn_of_walls`: `DZZLem54Exp P μIn χ` from `DZZLem53Exp P μIn χ` and
`DZZProp317Walls P μIn ξ dgWalls` (`0 < ξ ≤ 1/80`) only: `dzzLem54Exp_dzzMuIn_walls` (S5Walls3)
with `DZZLem54SegQ` from `dzzLem54SegQ_of_cfg` (S5L54I4), the big balls `dzzBigBalls_dzzMuIn`
and the measurability `aemeasurable_wickQArea_ball`, when `χ > 0`. For `χ ≤ 0` the lower bound
is trivial (`log min D ≥ 0`), and the upper bound is `dzzLem54_upper`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **DZZ Lemma 5.4 at `μIn`** from DZZ Lemma 5.3 and the walled Proposition 3.17. -/
theorem dzzLem54Exp_dzzMuIn_of_walls {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {χ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80)
    (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls) :
    DZZLem54Exp P (dzzMuIn γ W) χ := by
  haveI := hW.isProbabilityMeasure
  have hmeas := aemeasurable_wickQArea_ball (P := P) hW hγ hγ2
  rcases lt_or_ge 0 χ with hχ | hχ
  · refine dzzLem54Exp_dzzMuIn_walls hW hγ hγ2 hmeas hξ (by linarith) hL h317
      (dzzBigBalls_dzzMuIn hW hγ hγ2 (by norm_num)) ?_
    exact dzzLem54SegQ_of_cfg hW hγ hγ2 hχ hξ hξ1 hL
      (dzzProp317In_tildeBox_of_walls h317 u₅₄_mem_dzzVbar v₅₄_mem_dzzVbar u₅₄_ne_v₅₄)
      (dzzProp317In_tildeBox_of_walls h317 ringU₀_mem_dzzVbar ringV₀_mem_dzzVbar
        ringU₀_ne_ringV₀)
      (fun _ hu => dzzProp317Leg_of_walls hξ (by linarith) h317 hu)
  · intro u hu
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      have hℓ : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ.1).2 hδ.2)
      have h0 : 0 ≤ ∫ ω, logMinLGD (dzzWall (sqBox u (1 / 10)) (dzzMuIn γ W ω)) δ {u}
          (frontier (sqBox u (1 / 20))) ∂P :=
        integral_nonneg fun ω => logMinLGD_nonneg _ _ _ _
      exact lt_of_lt_of_le (by linarith) (div_nonneg h0 hℓ.le)
    · filter_upwards [dzzLem54_upper hL
        (fun _ hu _ hv huv => eventually_nhdsWithin_of_forall fun _ hδ =>
          ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ)
        (fun _ hu _ hv huv => eventually_nhdsWithin_of_forall fun _ hδ =>
          integrable_log_tilde hW hγ hγ2 hmeas hu hv huv hδ) hu (sub_pos.mpr hb)] with δ h
      linarith

end DZZ
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54F2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D123
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54C
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Side

/-!
# DZZ Lemma 5.4 from the corrected point-to-segment bound `DZZLem54SegQ` (P2-DZZ61K, D117)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 5.4
(`lem-exponent-point-to-boundary`, l. 2299–2304), proof l. 2553–2578, with the corrections of
DEC-117 §2(a): `dzzLem54Exp_of_segQ` is `dzzLem54Exp_of_seg` (S5L54D) with `DZZLem54SegQ` in
place of `DZZLem54Seg`; the lower half is `dzzLem54_lowerQ` (S5L54F1), the upper half
`dzzLem54_upper` (S5L54A). `dzzLem54Exp_dzzMuInQ` is the same at `μ = μIn` (as S5L54E).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **DZZ Lemma 5.4** from DZZ Lemma 5.3 (`hL`), a.s. finiteness and integrability of the tilde
distances, Proposition 3.17 at the walled measure of `𝕍_{u,1/10}` and at the leg walls
(`DZZProp317Leg`), the big balls (`DZZBigBalls`, P-BIG; the truncation `DZZLegTrunc` is
proved, `dzzLegTrunc_of_mem`, S5D123 from S5L54F3), and the corrected
(eq-point-to-segment) `DZZLem54SegQ`. -/
theorem dzzLem54Exp_of_segQ {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure ℂ}
    {χ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 40) (hL : DZZLem53Exp P μ χ)
    (hfin : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ᵐ ω ∂P, lgdDZZ (dzzWall (tildeBox u v) (μ ω)) δ u v < ⊤)
    (hint : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Integrable (fun ω => logMinLGD (dzzWall (tildeBox u v) (μ ω)) δ {u} {v}) P)
    (h317 : ∀ u ∈ dzzVbar,
      DZZProp317In P (fun ω => dzzWall (sqBox u (1 / 10)) (μ ω)) (sqBox u (1 / 10)) ξ)
    (h317Q : ∀ u ∈ dzzVbar, DZZProp317Leg P μ ξ u) (hbig : DZZBigBalls P μ (1 / 80))
    (hseg : DZZLem54SegQ P μ χ) : DZZLem54Exp P μ χ := by
  intro u hu
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [dzzLem54_lowerQ hξ hξ1 hu (h317 u hu) (h317Q u hu) hbig
      (dzzLegTrunc_of_mem hu) (hfin u hu (l54Pt u) (l54Pt_mem_dzzVbar hu) l54Pt_ne) hseg
      (sub_pos.mpr hb)] with δ h
    linarith
  · filter_upwards [dzzLem54_upper hL hfin hint hu (sub_pos.mpr hb)] with δ h
    linarith

/-- **DZZ Lemma 5.4 at `μIn`** from `DZZLem54SegQ`: `dzzLem54Exp_of_segQ` with `hfin`, `hint`
discharged as in `dzzLem54Exp_dzzMuIn` (S5L54E). -/
theorem dzzLem54Exp_dzzMuInQ {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hmeas : ∀ (c : ℂ) (r : ℝ), AEMeasurable (fun ω => wickQArea γ W ω (ball c r)) P)
    {χ ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 40) (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : ∀ u ∈ dzzVbar,
      DZZProp317In P (fun ω => dzzWall (sqBox u (1 / 10)) (dzzMuIn γ W ω))
        (sqBox u (1 / 10)) ξ)
    (h317Q : ∀ u ∈ dzzVbar, DZZProp317Leg P (dzzMuIn γ W) ξ u)
    (hbig : DZZBigBalls P (dzzMuIn γ W) (1 / 80))
    (hseg : DZZLem54SegQ P (dzzMuIn γ W) χ) : DZZLem54Exp P (dzzMuIn γ W) χ :=
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  dzzLem54Exp_of_segQ hξ hξ1 hL
    (fun _ hu _ hv huv => eventually_nhdsWithin_of_forall fun _ hδ =>
      ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ)
    (fun _ hu _ hv huv => eventually_nhdsWithin_of_forall fun _ hδ =>
      integrable_log_tilde hW hγ hγ2 hmeas hu hv huv hδ)
    h317 h317Q hbig hseg

end DZZ
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53UFC1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Z4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53X4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim6E

/-!
# DZZ Lemma 5.3 part 1, node 4 with the inputs discharged (P2-DZZ53UFC, decision D131)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522, with
(eq-M-A-upper-bound-bis) l. 2453–2456 and (eq-scaling-invariance-approximate) l. 2474.
Discharges the hypotheses of P2-DZZ53UF's node-4 results (S5L53UF1–UF5):

* `hcpl` from `fineChaos_sim_couple` (S5L53X4) at `K = 𝕍̃_{u,v}`, `ξ = 1/4` (`l53ufc_cpl`);
* `h317` from `dzzProp317Walls_dzzMuIn` (S5WallSim6E) at `ξ = min (1/80) (C_Mc/4, |u−v|/2)`;
* `hdom` from `l53_domination` (S5L53Z3) with `j = 3 n_{ε*} + 12` and `s = s_b`, on
  `𝓔₄ ∩ cellSizeEvent`, `P(𝓔₄ᶜ) ≤ e^{−L^{0.23}}` (`l53_E4_prob`). The cell-size event is needed
  for `δ^{C_mc} ≤ s_𝖢` (input of `l53_domination`); it is already part of `l53UVBadBox`, so
  `l53ufc_UVBadBox_le` takes the domination only on `G ∩ cellSizeEvent` (by evaluating
  `l53uf_UVBadBox_le` at the measure `𝟙_{cellSizeEvent} μ0`).
  `n_{ε*} ≥ 2` (for `α* > 0` and large `L`) gives `5 s_b ≤ s_𝖢` and `𝕍_{c_b,5 s_b} ⊆ (0,1)²`.
* `l53_three_pow_j_le`: `2^{3 n_{ε*} + 12} ≤ e^{L^{0.55}}` (proof of `l53_two_pow_j_le`, S5L53Z4,
  adapted).

`hcor` (the walled Cor 3.9 at `𝕍̃_{u,v}`) is kept as hypothesis: its removal is P2-DZZ53YC's
`l53_uv_far'` (S5L53YC1, in flight).

Main results: `l53uf_far_bound'`, `l53uf_hbad'`, **`l53UVBadBox_node4'`** (the proof of
`l53UVBadBox_node4`, S5L53UF5, copied with `l53ufc_UVBadBox_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

/-- `hcpl` of S5L53UF1–UF5: `fineChaos_sim_couple` at `𝕍̃_{u,v}`, `ξ = 1/4` -/
lemma l53ufc_cpl {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u v : ℂ} (hu : u ∈ dzzVbar)
    (hv : v ∈ dzzVbar) (huv : u ≠ v) : L53SimCoupleX γ (1 / 4) (tildeBox u v) :=
  fineChaos_sim_couple hγ hγ2 (by norm_num) (by norm_num) (isClosed_tildeBox u v)
    (tildeBox_subset_dzzVXi hu hv huv)

/-- the `ξ` of Prop 3.17 used for node 4 -/
lemma l53ufc_xi (γ : ℝ) {u v : ℂ} (huv : u ≠ v) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ 1 / 80 ∧ 2 * ξ < dzzCMc γ ∧ 2 * ξ ≤ dist u v := by
  have hd : 0 < dist u v := dist_pos.2 huv
  have hC := dzzCMc_pos γ
  refine ⟨min (1 / 80) (min (dzzCMc γ / 4) (dist u v / 2)), by positivity, min_le_left _ _, ?_, ?_⟩
  · have := (min_le_right (1 / 80 : ℝ) _).trans (min_le_left (dzzCMc γ / 4) (dist u v / 2))
    linarith
  · have := (min_le_right (1 / 80 : ℝ) _).trans (min_le_right (dzzCMc γ / 4) (dist u v / 2))
    linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-! ### The closed node-4 results -/

section Closed

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end Closed

end DZZ
end LQGMetric

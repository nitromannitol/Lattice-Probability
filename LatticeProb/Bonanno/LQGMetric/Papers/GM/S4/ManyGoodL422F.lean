/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodL422F at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422E
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodP412

/-!
# GM Lemma 4.22 on `ℰ_𝕣`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, Lemma 4.22 (`lem-holder-balls0`,
l. 2527–2535; proof l. 2541–2565), with the time unit `𝔲 = τ_{ℓ𝕣}(𝕫)` and
`K = ⌊(a/c₂)ε^{-β}⌋ − 1` of D-B1 / DV-B12 (GM.L4.22′ of DEC-B).

`gm_L4_22`: for `β < χ`, `λ₄ > 1`, `a ≤ ℓ` there is `ε₁ > 0` such that for `ε < ε₁`, on `ℰ_𝕣`
(at an `ω` where also `D_h` is a length metric with bounded balls and geodesics from `𝕫`, and
`H = h_·(·)` at `(𝕣, 0)`, `(𝕣, 𝕫)` — all a.s. properties), for every `k ∈ [0,K]` and every `z` with
`λ₄ε𝕣 ≤ dist(z, 𝓑^•_{t_k}) ≤ 2λ₄ε𝕣` (the closed range of `𝒵_k`, GM (4.10)):
`sup_{u ∈ ∂B_{2λ₄ε𝕣}(z)} D_h(𝕫, u; 𝓑^•_{s_{k+1}} ∖ cl B_{ε𝕣}(z)) ≤ t_k + N (ε/4)^χ 𝔠_𝕣e^{ξh_𝕣(0)}`,
`N = ⌈16πλ₄⌉` — GM (4.39) with the Hölder unit `𝔠_𝕣e^{ξh_𝕣(0)}` of condition 3 (GM write
`h_𝕣(𝕫)`, equivalent on `ℰ_𝕣` by condition 4; the event `{s_{k+1} ≤ τ_{2ℓ𝕣}}` of `F_k` is GM
(4.36), `gm_S4_3`).

The smallness of `ε` is used for: `t_k + N(ε/4)^χ S + (ε/2)^χ S < s_{k+1}` (GM (4.40), from
`β < χ` and `τ_{ℓ𝕣} ≥ (a/2)^{χ'} S`, GM.S4.11 (i) of DEC-B), the circle staying in
`B_{4ℓ𝕣}(𝕣V)` (where condition 3 holds), `ε/2 ≤ a` and `2λ₄ε < a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `c₀ ε^χ < ε^β − ε^{2β}` for small `ε` when `0 < β < χ` -/
theorem gm_small_gap {β χ c₀ : ℝ} (hβ : 0 < β) (hβχ : β < χ) (hc₀ : 0 < c₀) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), c₀ * ε ^ χ < ε ^ β - ε ^ (2 * β) := by
  have t1 : Tendsto (fun ε : ℝ => ε ^ (χ - β)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 (χ - β) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun ε : ℝ => ε ^ β) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto
    rw [Real.zero_rpow hβ.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have e1 := t1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * c₀) by positivity))
  have e2 := t2.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [e1, e2, self_mem_nhdsWithin] with ε h1 h2 hε
  have hε0 : 0 < ε := hε
  have hb : 0 < ε ^ β := Real.rpow_pos_of_pos hε0 _
  have h2b : ε ^ (2 * β) = ε ^ β * ε ^ β := by
    rw [← Real.rpow_add hε0]; ring_nf
  have hχ' : ε ^ χ = ε ^ (χ - β) * ε ^ β := by
    rw [← Real.rpow_add hε0]; ring_nf
  rw [h2b, hχ']
  have : c₀ * ε ^ (χ - β) < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * c₀)] at h1; linarith
  nlinarith

end LQGMetric.GM

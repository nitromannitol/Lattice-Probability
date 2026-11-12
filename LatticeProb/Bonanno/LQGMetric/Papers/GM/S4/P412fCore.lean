/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412fCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fIn
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eCore
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eExt
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412bRate

/-!
# GM Proposition 4.12 on a good `k`, with the deterministic inputs discharged on `ℰ_𝕣`

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Proposition 4.12,
l. 2229–2276, and L4.15 Step 3 (l. 2160–2163).

`p412f_core`: on `ℰ_𝕣`, for small dyadic `ε` and `k ≤ K`, for `𝕫 ∈ 𝕣U`, `|𝕫 − 𝕨| ≥ 4ℓ𝕣`
and the geodesic `P = sel 𝕫 𝕨 (h ω)`: if the arcs of `Conf_k` cover `∂𝓑^•_{t_k}` (GM.S4.1),
`E` contains the endpoints of all arcs of `Conf_k` (GM l. 2153 `𝒴_k`), every `e ∈ E` has a
Step 3 centre `z_e` with (∗) at scale `ε^κ𝕣` (`p412eGoodZ`), and `P` does not enter
`B_{17ε^κ𝕣}(z_e) ∖ 𝓑^•_{t_k}` (GM's events `G_y`, property A, l. 2166–2168, D-V `DV-Gy-17`),
then `𝒵^E_k ≠ ∅`.

Inputs discharged here (all from `ℰ_𝕣`, `p412f_times`): the unit-speed form of `P`
(`geodL`), `t_k < s_{k+1} ≤ |P|` (l. 2246), `P(t_k) ∈ ∂𝓑^•_{t_k}` and the arc `I_k ∋ P(t_k)`
(l. 2249), `F = 𝓑^•_{s_{k+1}}` with `B_{16ε^κ𝕣}(𝓑^•_{t_k}) ⊆ F` (l. 2160), the exit time
`b = |P|`, the region hypotheses (`𝓑^•_{t_k} ⊆ B_{2ℓ𝕣}(𝕫)`, l. 2140), `d₀ = (3/2)λ₄ε𝕣`
(l. 2234–2237), and the smallness of `ε' = (ε^κ/2)^{χ'/χ}` (l. 2249).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the smallness conditions on `ε` used in `p412f_core` -/
theorem p412f_small {a κ ℓ lam p χ χ' : ℝ} (ha : 0 < a) (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hp : 0 < p) (hχ : 0 < χ) :
    ∃ ε₃ : ℝ, 0 < ε₃ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₃, ε ≤ a ∧ 17 * ε ^ κ ≤ a ∧
      4 * lam * ε < 2 * ℓ ∧ (ε ^ κ / 2) ^ p ≤ 1 ∧ (ε ^ κ / 2) ^ p ≤ a ∧
      ((ε ^ κ / 2) ^ p) ^ χ < a ^ χ' := by
  have t0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have tκ : Tendsto (fun ε : ℝ => ε ^ κ) (𝓝[>] (0 : ℝ)) (𝓝 0) := t0.rpow_const_nhds_zero hκ
  have t17 : Tendsto (fun ε : ℝ => 17 * ε ^ κ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tκ.const_mul 17
  have t4 : Tendsto (fun ε : ℝ => 4 * lam * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using t0.const_mul (4 * lam)
  have tg : Tendsto (fun ε : ℝ => ε ^ κ / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tκ.div_const 2
  have tp : Tendsto (fun ε : ℝ => (ε ^ κ / 2) ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tg.rpow_const_nhds_zero hp
  have tpχ : Tendsto (fun ε : ℝ => ((ε ^ κ / 2) ^ p) ^ χ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tp.rpow_const_nhds_zero hχ
  have ev := (((((t0.eventually (Iic_mem_nhds ha)).and (t17.eventually (Iic_mem_nhds ha))).and
    (t4.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 2 * ℓ)))).and
    (tp.eventually (Iic_mem_nhds one_pos))).and (tp.eventually (Iic_mem_nhds ha))).and
    (tpχ.eventually (gt_mem_nhds (Real.rpow_pos_of_pos ha χ')))
  obtain ⟨ε₃, hε₃, H⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 ev
  refine ⟨ε₃, hε₃, fun ε hε => ?_⟩
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := H hε
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- `cthickening δ K ⊆ 𝕣V^{4ℓ𝕣}` when `K ⊆ B_{2ℓ𝕣}(𝕫)`, `𝕫 ∈ 𝕣V`, `δ < 2ℓ𝕣` -/
theorem p412f_cth_reg {R : RegPar} {𝕣 : ℝ} {𝕫 : ℂ} (h𝕫 : 𝕫 ∈ rScale 𝕣 R.V) {K : Set ℂ}
    (hK : K ⊆ ball 𝕫 (2 * (R.ℓ * 𝕣))) (hℓ𝕣 : 0 < R.ℓ * 𝕣) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ < 2 * (R.ℓ * 𝕣)) : cthickening δ K ⊆ regRegion R 𝕣 := by
  intro x hx
  have h1 := cthickening_subset_of_subset δ (hK.trans ball_subset_closedBall) hx
  rw [cthickening_closedBall hδ0 (by positivity)] at h1
  exact mem_thickening_iff.2 ⟨𝕫, h𝕫, lt_of_le_of_lt (mem_closedBall.1 h1) (by linarith)⟩

/-- `ε₂ = 2((ε^κ/2)^{χ'/χ})^{χ/χ'}𝕣 = ε^κ𝕣` -/
theorem p412f_eps2 {ε κ χ χ' 𝕣 : ℝ} (hε : 0 < ε) (hχ : 0 < χ) (hχ' : 0 < χ') :
    2 * ((ε ^ κ / 2) ^ (χ' / χ)) ^ (χ / χ') * 𝕣 = ε ^ κ * 𝕣 := by
  rw [← Real.rpow_mul (by positivity), div_mul_div_comm, mul_comm χ' χ,
    div_self (by positivity), Real.rpow_one]
  ring

end LQGMetric.GM

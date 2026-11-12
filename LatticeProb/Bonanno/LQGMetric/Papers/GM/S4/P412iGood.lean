/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iGood at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iCond
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fCore
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fIn
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fEnd
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412Step12
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGoodL422F

/-!
# GM L4.15 Step 4: `ℰ ∩ Badᶜ ∩ A_k ⊆ {𝒵^E_k ≠ ∅}` (input `hgood` of `gm_L4_15_step4_rate`)

Source: GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
L4.15 Step 4, l. 2195–2199 ("By (4.39), on `ℰ_𝕣` we have `σ_k ≤ s_{k+1}` …; by (4.40), … except on an
event of probability `o^∞_ε(ε)` we have `#Conf_k ≤ ε^{-ω}`"), and the end of the proof of
Lemma 4.15 / Prop 4.12 (l. 2212–2276, `p412f_good_near`).

**`p412i_good_k`**: on `ℰ_𝕣`, for small dyadic `ε`, CONF scale `δ = 2^{-m} ∈ [18ε^κ, 36ε^κ]`:
if `ω ∈ A_k = (⋂_{j<N} G_j) ∪ {σ_k > s_{k+1}} ∪ {#Conf_k > L}` and `#Conf_k ≤ L`, the `G_j` have
CONF L3.6 property A at the centres `x_j`, and the centres cover the endpoints `𝒴_k` in the sense of
(∗) (`p412f_good_near`), then `𝒵^E_k ≠ ∅`. The event `{σ_k > s_{k+1}}` is excluded by (4.39)
(`p412_eq439` at `κ/2`, as in `p412f_propA`; DV-L36-dyadic).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `36 t^κ ≤ t^{κ/2}` for small `t > 0` -/
theorem p412i_small_pow {κ : ℝ} (hκ : 0 < κ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁, 36 * ε ^ κ ≤ ε ^ (κ / 2) := by
  have hc := (Real.continuousAt_rpow_const 0 (κ / 2) (Or.inr (by linarith))).tendsto
  rw [Real.zero_rpow (by linarith : κ / 2 ≠ 0)] at hc
  obtain ⟨ε₁, hε₁, hb⟩ := Metric.tendsto_nhds_nhds.1 hc (1 / 36) (by norm_num)
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, fun ε hε => ?_⟩
  have hε0 := hε.1
  have h1 : dist ε 0 < ε₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε0]; exact lt_of_lt_of_le hε.2 (min_le_left _ _)
  have h2 := hb h1
  rw [Real.dist_eq, sub_zero, abs_of_pos (Real.rpow_pos_of_pos hε0 _)] at h2
  have e : ε ^ κ = ε ^ (κ / 2) * ε ^ (κ / 2) := by
    rw [← Real.rpow_add hε0]; ring_nf
  rw [e]
  have h3 : 0 < ε ^ (κ / 2) := Real.rpow_pos_of_pos hε0 _
  nlinarith

end LQGMetric.GM

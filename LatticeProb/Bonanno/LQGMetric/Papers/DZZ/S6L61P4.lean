/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61P4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61P3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61H3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61E
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Side
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcL5

/-!
# DZZ Lemma 6.1, lower half, at `μIn` (P2-DZZ61P)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 6.1, l. 2584–2608.
`dzzLem61Lower_of_glue` (S6L61E) with its inputs discharged:
* Proposition 3.17 at `μIn`: `dzzProp317_dzzMuIn` (S3ConcL5), `0 < ξ < C_Mc(γ)`;
* (eq-point-to-boundary-kappa), lower half, moving centres: `dzzL61PtBdry_dzzMuIn` (S6L61P3);
* the gluing of Fig. glue at segment length `δ^{2ι/χ}`: `dzzL61GlueK_of_lem53` (S6L61H3);
* `hfin`: `ae_wickQArea_reg` + `lgdDZZ_lt_top_openSquare`; the tilde `hfin` of the gluing:
  `ae_lgd_tilde_lt_top` (S5L53Side).

Remaining hypotheses: DZZ Lemma 5.4 (`DZZLem54Exp`), DZZ Lemma 5.3 (`DZZLem53Exp`) and the walled
Proposition 3.17 at the fixed tilde box `𝕍̃_{u₀,v₀}` of the gluing (DZZ Remark 5.2; open,
DEC-117 §3), as required by `dzzL61GlueK_of_lem53`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-- `hfin` of `dzzLem61Lower_of_glue` at `μIn` -/
theorem dzzMuIn_lgd_lt_top_sqBox {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ u ∈ dzzVbar, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, ∀ x ∈ sqBox u (1 / 20),
      ∀ y ∈ sqBox u (1 / 20), lgdDZZ (dzzMuIn γ W ω) δ x y < ⊤ := by
  intro u hu
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  filter_upwards [ae_wickQArea_reg hW hγ hγ2] with ω hω
  obtain ⟨hK, hat⟩ := hω
  have hw : ∀ K ⊆ openSquare, dzzMuIn γ W ω K = wickQArea γ W ω K := fun K hK' => by
    rw [dzzMuIn, dzzWall_apply_of_subset isClosed_dzzV.measurableSet
      (hK'.trans fun z hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩)]
  obtain ⟨hu1, hu2⟩ := near_of_mem_dzzVbar hu
  have hS : ∀ z ∈ sqBox u (1 / 20), z ∈ openSquare := fun z hz => by
    obtain ⟨h1, h2⟩ := hz
    have e1 := abs_sub_le z.re u.re (1 / 2)
    have e2 := abs_sub_le z.im u.im (1 / 2)
    have r1 : |z.re - 1 / 2| < 1 / 2 := by linarith
    have r2 : |z.im - 1 / 2| < 1 / 2 := by linarith
    rw [abs_lt] at r1 r2
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  intro x hx y hy
  exact lgdDZZ_lt_top_openSquare (fun K hKc hKs => by rw [hw K hKs]; exact hK K hKc hKs)
    (fun z hz => by rw [hw {z} (singleton_subset_iff.mpr hz)]; exact hat z hz) hδ (hS x hx)
    (hS y hy)

/-- **DZZ Lemma 6.1, lower half, at `μIn`** (l. 2593–2608) from DZZ Lemmas 5.3, 5.4 and the
walled Proposition 3.17 at the fixed tilde box of the gluing. -/
theorem dzzLem61Lower_dzzMuIn {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {α χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h54 : DZZLem54Exp P (dzzMuIn γ W) χ) (hL53 : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317w : ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ 1 / 80 ∧
      DZZProp317In P (fun ω => dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
        (tildeBox ringU₀ ringV₀) ξ) :
    DZZLem61Lower P (dzzMuIn γ W) α χ := by
  haveI := hW.isProbabilityMeasure
  by_cases hχ : χ ≤ 0
  · intro u _ ε hε
    filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    have hL : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ.1).mpr hδ.2)
    exact (by linarith : χ - ε < 0).trans_le
      (div_nonneg (integral_nonneg fun ω => logMinLGD_nonneg _ _ _ _) hL.le)
  push_neg at hχ
  obtain ⟨ξ, hξ, hξ1, h317⟩ := h317w
  have hμ : ∀ (c : ℂ) (r : ℝ), AEMeasurable (fun ω => dzzMuIn γ W ω (Metric.ball c r)) P :=
    fun c r => by
      simp only [dzzMuIn, dzzWall, Measure.add_apply, Measure.smul_apply]
      exact (aemeasurable_wickQArea_ball hW hγ hγ2 c r).add aemeasurable_const
  have hfinT : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      lgdDZZ (dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω)) δ ringU₀ ringV₀ < ⊤ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ae_lgd_tilde_lt_top hW hγ hγ2 ringU₀_mem_dzzVbar ringV₀_mem_dzzVbar ringU₀_ne_ringV₀ hδ
  refine dzzLem61Lower_of_glue hα0 hα1 (dzzCMc_pos γ) hμ
    (fun ξ' hξ' hξ'c => dzzProp317_dzzMuIn hW hγ hγ2 hξ' hξ'c)
    (dzzMuIn_lgd_lt_top_sqBox hW hγ hγ2)
    (fun u hu => dzzL61PtBdry_dzzMuIn hW hγ hγ2 hα0 hα1 h54 hu) fun u hu => ?_
  refine ⟨χ / 2, by positivity, fun ι hι => ?_⟩
  have hκ : 0 < 2 * ι / χ := div_pos (by linarith [hι.1]) hχ
  exact dzzL61GlueK_of_lem53 hW hγ hγ2 hα1 hι.1 hκ
    (by rw [div_mul_cancel₀ _ hχ.ne']) (by rw [div_lt_one hχ]; linarith [hι.2]) hξ hξ1 hu
    hL53 h317 hfinT

/-- The form consumed by DG (`α = 5/8`, DG:1627). -/
theorem dzzLem61Lower_dzzMuIn_five_eighths {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ}
    (h54 : DZZLem54Exp P (dzzMuIn γ W) χ) (hL53 : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317w : ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ 1 / 80 ∧
      DZZProp317In P (fun ω => dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
        (tildeBox ringU₀ ringV₀) ξ) :
    DZZLem61Lower P (dzzMuIn γ W) (5 / 8) χ :=
  dzzLem61Lower_dzzMuIn hW hγ hγ2 (by norm_num) (by norm_num) h54 hL53 h317w

end DZZ
end LQGMetric

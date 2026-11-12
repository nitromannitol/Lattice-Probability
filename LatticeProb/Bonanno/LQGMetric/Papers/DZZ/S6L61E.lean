/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61E at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117

/-!
# DZZ Lemma 6.1, lower half, with the corrected segment length `δ^{2ι/χ}` (P2-DZZ61K, D117)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 6.1, l. 2593–2608.
DZZ take segments `L_δ ⊆ ∂𝕍̄_{u,α}` of length `δ^{2ι}` (l. 2601) and bound the four short crossings
of Fig. glue (l. 2605) by `δ^{−χ+ι}`. At scale `|L_δ| = δ^κ` the crossings cost
`δ^{−χ(1−κ)+o(1)}`, which is `≤ δ^{−(χ−ι)}` only when `κχ ≥ 2ι`; DZZ's `κ = 2ι` needs `χ ≥ 1/2`
(DEC-117 §2(c), DV-D117 item 1). We use `κ = 2ι/χ`:

* `dzzL61SegBound_of_glueK`: `DZZL61SegBound P μ α χ u ι κ` from `DZZL61GlueK P μ α χ u ι κ`
  (the contradiction of l. 2605–2608, `dzzL61SegBound_of_glue`, S6L61D);
* `dzzLem61Lower_of_glue`: **DZZ Lemma 6.1, lower half** from `DZZL61GlueK` at `κ = 2ι/χ` for all
  small `ι` (with the union bound `dzzLem61Lower_of_segBound`, S6L61B, over `≈ δ^{−2ι/χ}`
  segments). For `χ ≤ 0` the segment bound is trivial (`logMinLGD ≥ 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The segment bound of DZZ Lemma 6.1** (l. 2601–2608) at segment length `δ^κ`, from
`DZZL61GlueK` (DEC-117 §2(c)), (eq-point-to-boundary-kappa) and Proposition 3.17. -/
theorem dzzL61SegBound_of_glueK {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure ℂ}
    {α χ ξ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hξ : 0 < ξ) (hξα : ξ ≤ (1 - α) / 40)
    (h317 : DZZProp317 P μ ξ) {u : ℂ} (hu : u ∈ dzzVbar) {ι : ℝ} (hι : 0 < ι) (hι1 : ι < 1)
    {κ : ℝ} (hκ0 : 0 < κ) (hκξ : κ < ξ)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, ∀ x ∈ sqBox u (1 / 20), ∀ y ∈ sqBox u (1 / 20),
      lgdDZZ (μ ω) δ x y < ⊤)
    (hpt : DZZL61PtBdry P μ α χ u) (hglue : DZZL61GlueK P μ α χ u ι κ) :
    DZZL61SegBound P μ α χ u ι κ :=
  dzzL61SegBound_of_glue hα0 hα1 hξ hξα h317 hu hι hι1 hκ0 hκξ hfin hpt hglue

/-- **DZZ Lemma 6.1, lower half** (l. 2593–2608) from DZZ Proposition 3.17, the lower half of
(eq-point-to-boundary-kappa) (`DZZL61PtBdry`), the gluing of Fig. glue at segment length
`δ^{2ι/χ}` (`DZZL61GlueK`, small `ι`; DEC-117 §2(c)) and a.s. finiteness of `D_δ` on `𝕍̄_u`. -/
theorem dzzLem61Lower_of_glue {P : Measure Ω} [IsProbabilityMeasure P] {μ : Ω → Measure ℂ}
    {α χ ξ₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hξ₀ : 0 < ξ₀)
    (hμ : ∀ c r, AEMeasurable (fun ω => μ ω (Metric.ball c r)) P)
    (h317 : ∀ ξ, 0 < ξ → ξ < ξ₀ → DZZProp317 P μ ξ)
    (hfin : ∀ u ∈ dzzVbar, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P, ∀ x ∈ sqBox u (1 / 20),
      ∀ y ∈ sqBox u (1 / 20), lgdDZZ (μ ω) δ x y < ⊤)
    (hpt : ∀ u ∈ dzzVbar, DZZL61PtBdry P μ α χ u)
    (hglue : ∀ u ∈ dzzVbar, ∃ ι₁ > 0, ∀ ι ∈ Ioo (0 : ℝ) ι₁,
      DZZL61GlueK P μ α χ u ι (2 * ι / χ)) :
    DZZLem61Lower P μ α χ := by
  refine dzzLem61Lower_of_segBound hα0 hα1 hξ₀ hμ h317 fun u hu => ?_
  by_cases hχ : χ ≤ 0
  · -- trivial segment bound: `(χ − 2ι) log δ⁻¹ ≤ 0 ≤ E log min D`
    refine ⟨1, one_pos, fun ι hι L _ => ?_⟩
    filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
    have hL : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ.1).mpr hδ.2)
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith [hι.1]) hL.le).trans
      (integral_nonneg fun ω => logMinLGD_nonneg _ _ _ _)
  push_neg at hχ
  set ξ := min (ξ₀ / 2) ((1 - α) / 40) with hξdef
  have hξ : 0 < ξ := lt_min (by linarith) (by linarith)
  have hξ₀' : ξ < ξ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hξα : ξ ≤ (1 - α) / 40 := min_le_right _ _
  obtain ⟨ι₁, hι₁, hg⟩ := hglue u hu
  refine ⟨min ι₁ (min (ξ * χ / 4) (1 / 2)),
    lt_min hι₁ (lt_min (by positivity) (by norm_num)), fun ι hι => ?_⟩
  have h1 : ι < ι₁ := hι.2.trans_le (min_le_left _ _)
  have h2 : ι < ξ * χ / 4 := hι.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : ι < 1 / 2 := hι.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hκ0 : 0 < 2 * ι / χ := div_pos (by linarith [hι.1]) hχ
  have hκξ : 2 * ι / χ < ξ := by
    rw [div_lt_iff₀ hχ]; nlinarith
  exact dzzL61SegBound_of_glueK hα0 hα1 hξ hξα (h317 ξ hξ hξ₀') hu hι.1 (by linarith) hκ0 hκξ
    (hfin u hu) (hpt u hu) (hg ι ⟨hι.1, h1⟩)

end DZZ
end LQGMetric

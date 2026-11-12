/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiC2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiC1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeasExp
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiA2

/-!
# D129 packet P-129C, part 2: `χ > 0` (P2-CHIC)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Lemma 2.12 (`lem-obvious-bounds`),
l. 740–759, lower half `c − o(1) < E log D_{γ,δ}(u,v) / log δ⁻¹`, applied to the tilde distance
`D̃_δ(u,v)` of DZZ l. 2265–2270 (balls inside `𝕍̃_{u,v}`, measure `μIn`), and DZZ Lemma 5.3
(`lem-existence-exponent`, l. 2292–2297): `χ = lim E log D̃_δ / log δ⁻¹ ≥ c > 0`.

* `dzz_lemma212_lower_tilde`: DZZ L2.12 lower half for `D̃`, from `dzz_lemma212_lower_exp_integral`
  (LGDMeasExp) with the ball-size input `ballMassLowerTail_dzzMuIn` (S5ChiC1, DV-D129-4; the wall
  only increases ball masses), a.s. finiteness `ae_lgd_tilde_lt_top` and integrability
  `integrable_log_tilde` (S5L53Side), measurability `aemeasurable_wickQArea_ball` (S5L53B1);
* `chi_pos_of_lem53`: `χ > 0` (DZZ Thm 1.1 / l. 759 "`χ > 0`" via L2.12), at the reference pair
  `chiRefU, chiRefV ∈ 𝕍̄` (S5ChiA2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

lemma mem_openSquare_of_mem_dzzVbar {u : ℂ} (hu : u ∈ dzzVbar) : u ∈ openSquare := by
  simp only [dzzVbar, sqBox, mem_ofPred_eq, abs_le] at hu
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hu
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ Lemma 2.12, lower half, for the tilde distance** `D̃_δ(u,v)` at `μIn`:
`E log D̃_δ(u,v) ≥ (c − ε) log δ⁻¹` for small `δ`. -/
theorem dzz_lemma212_lower_tilde (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      c - ε ≤ (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v} ∂P) /
        Real.log δ⁻¹ := by
  have := hW.isProbabilityMeasure
  have hbm : ∀ (c : ℂ) (r : ℝ), AEMeasurable
      (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω) (ball c r)) P := fun c r => by
    simp only [dzzWall, dzzMuIn, Measure.add_apply, Measure.smul_apply]
    exact ((aemeasurable_wickQArea_ball hW hγ hγ2 c r).add aemeasurable_const).add
      aemeasurable_const
  have hfin : ∀ δ : ℝ, 0 < δ → ∀ᵐ ω ∂P,
      lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v ≠ ⊤ := fun δ hδ => by
    filter_upwards [ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ] with ω hω using hω.ne
  have hint : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Integrable
      (fun ω => Real.log ((lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v).toNat : ℝ))
        P := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have := integrable_log_tilde hW hγ hγ2 (aemeasurable_wickQArea_ball hW hγ hγ2) hu hv huv
      (mem_Ioi.1 hδ)
    simpa only [logMinLGD_singleton] using this
  have hT : ∀ K : Set ℂ, IsCompact K → K ⊆ openSquare →
      BallMassLowerTail P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) K := by
    intro K hK hKV
    obtain ⟨p, A, C, r₀, hp, hA, hr₀, h⟩ := ballMassLowerTail_dzzMuIn hW hγ hγ2 hK hKV
    refine ⟨p, A, C, r₀, hp, hA, hr₀, fun w hw s hs hsr t ht =>
      (measure_mono ?_).trans (h w hw s hs hsr t ht)⟩
    intro ω hω
    exact (Measure.le_iff'.1 (le_dzzWall (tildeBox u v) (dzzMuIn γ W ω)) _).trans hω
  simp only [logMinLGD_singleton]
  exact dzz_lemma212_lower_exp_integral (mem_openSquare_of_mem_dzzVbar hu) huv hbm hfin hint hT

/-- **`χ > 0`** (DEC-129 §4, P-129C): the exponent of DZZ Lemma 5.3 at `μIn` is positive
(DZZ Lemma 2.12 lower half at the reference pair of `𝕍̄`). -/
theorem chi_pos_of_lem53 (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ}
    (hL : DZZLem53Exp P (dzzMuIn γ W) χ) : 0 < χ := by
  obtain ⟨c, hc, h⟩ := dzz_lemma212_lower_tilde hW hγ hγ2 chiRefU_mem chiRefV_mem chiRef_ne
  have hlim := hL _ chiRefU_mem _ chiRefV_mem chiRef_ne
  have := ge_of_tendsto hlim (h (c / 2) (by positivity))
  linarith

end DZZ
end LQGMetric

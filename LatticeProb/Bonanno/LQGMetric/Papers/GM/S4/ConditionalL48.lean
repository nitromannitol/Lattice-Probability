/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ConditionalL48 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStab
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupGeoBdy
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ConditionalGrid

/-!
# GM Lemma 4.8, pathwise count: `#𝒵_k(P)` on the event of GM Lemma 2.12

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Lemma 4.8
(`lem-good-annulus-count`, l. 1806–1822). On the event of GM Lemma 2.12 at centre `𝕫` for filled
balls (GM.S4.8, `gm_S4_8`, applied with `4λ₄ε` in place of `ε`), if `𝓑^•_{t_k} ⊆ B_R(𝕫)` and
`𝕨 ∉ 𝓑^•_{t_k}`, then every finite set `S` of pairs of `𝒵_k(P) = {(z,r) ∈ 𝒵_k : P ∩ B_r(z) ≠ ∅}`
satisfies `#S · σ² ≤ #Rads · V`, where `V` is the area bound of Lemma 2.12 and `σ ≤ λ₁ε^{1+ν}𝕣/4`,
`2σ ≤ r ≤ ε𝕣` for the radii (`gm_L4_8_count`). This is GM (4.19) pathwise; with
`V = (4λ₄ε)^{2−1/M'}𝕣²`, `σ ≍ ε^{1+ν}𝕣` and `#Rads ≤ μ log_8 ε^{-1}` it gives
`#𝒵_k(P) ≤ C ε^{-2ν-1/M'} log_8 ε^{-1}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- **GM (4.19), pathwise** (l. 1806–1822) -/
theorem gm_L4_8_count {D : ContMetric} {𝕫 𝕨 : ℂ} {t R : ℝ} {V : ℝ≥0∞}
    {lam1 lam4 ε ν 𝕣 σ : ℝ}
    (hgood : ∀ s : ℝ, 0 < s → filledBall D 𝕫 s ⊆ ball 𝕫 R → ∀ w : ℂ, w ∉ filledBall D 𝕫 s →
      ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL D G L 𝕫 w →
        volume (thickening (4 * lam4 * ε * 𝕣) (G '' Icc 0 L) ∩
          thickening (4 * lam4 * ε * 𝕣) (frontier (filledBall D 𝕫 s))) ≤ V)
    (ht : 0 < t) (hsub : filledBall D 𝕫 t ⊆ ball 𝕫 R) (hw : 𝕨 ∉ filledBall D 𝕫 t)
    {G : ℝ → ℂ} {L : ℝ} (hG : IsGeodesicL D G L 𝕫 𝕨)
    (hlam : 1 ≤ 2 * lam4) (hε𝕣 : 0 ≤ ε * 𝕣) (hσ : 0 < σ)
    (hσδ : σ ≤ lam1 * ε ^ (1 + ν) * 𝕣 / 4)
    (Rads : Finset ℝ) (hRads : ∀ r ∈ Rads, 2 * σ ≤ r ∧ r ≤ ε * 𝕣)
    (S : Finset (ℂ × ℝ))
    (hS : ∀ p ∈ S, p ∈ candSet (filledBall D 𝕫 t) lam1 lam4 ε ν 𝕣 (Rads : Set ℝ) ∧
      (G '' Icc 0 L ∩ ball p.1 p.2).Nonempty) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤ Rads.card * V := by
  have hz : 𝕫 ∈ filledBall D 𝕫 t := by
    refine Or.inl (subset_closure ?_)
    show D.1 (𝕫, 𝕫) < t
    rw [D.2.self_eq_zero]
    exact ht
  have hK : (frontier (filledBall D 𝕫 t)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨𝕫, hz⟩, fun h => hw (h ▸ mem_univ 𝕨)⟩
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2)
      ≤ Rads.card * volume (thickening (4 * lam4 * ε * 𝕣) (G '' Icc 0 L) ∩
          thickening (4 * lam4 * ε * 𝕣) (frontier (filledBall D 𝕫 t))) := by
        refine gm_pairs_card_le hσ hσδ S Rads (fun p hp => ?_) (fun p hp => ?_)
        · have h1 := (hS p hp).1
          exact ⟨h1.1, Finset.mem_coe.mp h1.2.2.1, (hRads _ (Finset.mem_coe.mp h1.2.2.1)).1⟩
        · have h1 := (hS p hp).1
          exact gm_ball_subset_count hlam hε𝕣 (hRads _ (Finset.mem_coe.mp h1.2.2.1)).2 hK
            h1.2.2.2.2 (hS p hp).2
    _ ≤ Rads.card * V := mul_le_mul_right (hgood t ht hsub 𝕨 hw G L hG) _

/-- **GM (4.19)** (l. 1806–1823): with superpolynomially high probability as `ε → 0`, uniformly in
`𝕣`, for every `t > 0` with `𝓑^•_t ⊆ B_{(4λ₄ε)^{-M}𝕣}(𝕫)` and `𝕨 ∉ 𝓑^•_t`, every geodesic `P`
from `𝕫` to `𝕨` and every finite set `S` of pairs of `𝒵_k(P)` (radii in `Rads`,
`2σ ≤ r ≤ ε𝕣`, `σ ≤ λ₁ε^{1+ν}𝕣/4`) satisfy `#S σ² ≤ #Rads (4λ₄ε)^{2−1/M} 𝕣²`.
From GM.S4.8 (`gm_S4_8U`, i.e. GM Lemma 2.12 at `4λ₄ε`) and `gm_L4_8_count`. The constants are
uniform in the probability space and in `𝕫, 𝕨` (D75; GM L4.7/L4.8: "the rates … are deterministic
and depend only on `M, μ, ν, {λ_i}`"). -/
theorem gm_L4_8_uncondU (hDF43 : DFGPSProp4_3F) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {M : ℝ} (hM : 0 < M)
    {lam1 lam4 ν : ℝ} (hlam : 1 ≤ 2 * lam4) :
    ∀ p : ℝ, 0 < p → ∃ C ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ 𝕫 𝕨 : ℂ, ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
    P ({ω | ∀ t : ℝ, 0 < t →
      filledBall (D (h ω)) 𝕫 t ⊆ ball 𝕫 ((4 * lam4 * ε) ^ (-M) * 𝕣) →
      𝕨 ∉ filledBall (D (h ω)) 𝕫 t → ∀ (G : ℝ → ℂ) (L : ℝ), IsGeodesicL (D (h ω)) G L 𝕫 𝕨 →
      ∀ σ : ℝ, 0 < σ → σ ≤ lam1 * ε ^ (1 + ν) * 𝕣 / 4 →
      ∀ Rads : Finset ℝ, (∀ r ∈ Rads, 2 * σ ≤ r ∧ r ≤ ε * 𝕣) →
      ∀ S : Finset (ℂ × ℝ), (∀ p ∈ S, p ∈ candSet (filledBall (D (h ω)) 𝕫 t) lam1 lam4 ε ν 𝕣
          (Rads : Set ℝ) ∧ (G '' Icc 0 L ∩ ball p.1 p.2).Nonempty) →
      (S.card : ℝ≥0∞) * ENNReal.ofReal (σ ^ 2) ≤
        Rads.card * ENNReal.ofReal ((4 * lam4 * ε) ^ (2 - 1 / M) * 𝕣 ^ 2)})ᶜ ≤ ENNReal.ofReal (C * ε ^ p) := by
  intro p hp
  obtain ⟨C, ε₀, hε₀, hC⟩ := gm_S4_8U hDF43 hγ hγ2 hD hM p hp
  have hl : 0 < 4 * lam4 := by linarith
  refine ⟨C * (4 * lam4) ^ p, ε₀ / (4 * lam4), div_pos hε₀ hl,
    fun {Ω} _ P _ h hh 𝕫 𝕨 ε hε 𝕣 h𝕣 => ?_⟩
  have hε' : 4 * lam4 * ε ∈ Ioo (0 : ℝ) ε₀ := by
    refine ⟨mul_pos hl hε.1, ?_⟩
    have := hε.2
    rw [lt_div_iff₀ hl] at this
    linarith
  refine le_trans (measure_mono (compl_subset_compl.mpr ?_))
    ((hC P h hh 𝕫 _ hε' 𝕣 h𝕣).trans (le_of_eq ?_))
  · intro ω hω t ht hsub hw G L hG σ hσ hσδ Rads hRads S hS
    exact gm_L4_8_count hω ht hsub hw hG hlam (mul_pos hε.1 h𝕣).le hσ hσδ Rads hRads S hS
  · rw [Real.mul_rpow hl.le hε.1.le, mul_assoc]

end LQGMetric.GM

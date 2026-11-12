/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_20Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20SqMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.20 (`Blueprint.DFGPSLem3_20`) from Lemma 3.19 (task P2-DFA7)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.20 (T:2317–2325), proof
T:2327–2330. First display: `L320.lem3_20_ball_of` (`L3_20Ball.lean`); second display:
`lem3_20_sq_of` below, from Lemma 3.19's square part with `s = (χ + ξ(Q−2))/2`, the union bound
over open dyadic squares of every level (`grid_union_bound`, `ρ = 1/2`) and `sq_display_det`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L320

open Blueprint Complex LQGDimension.LFPPRecords

/-- **DFGPS Lemma 3.20, second display**, from Lemma 3.19 (`eqn-ep-diam-square`) -/
theorem lem3_20_sq_of (h19 : Lem3_19SqU) : Lem3_20Sq := by
  intro γ hγ hγ2 D c hD K hK χ hχ hχQ
  have hξ : 0 < xiGamma γ := DG.xiGamma_pos hγ
  set ξ := xiGamma γ with hξ_def
  set s := (χ + ξ * (Q γ - 2)) / 2 with hs_def
  have hχs : χ < s := by rw [hs_def]; linarith
  have hsQ : s < ξ * (Q γ - 2) := by rw [hs_def]; linarith
  have hs0 : 0 < s := by linarith
  set α := (ξ * Q γ - s) ^ 2 / (2 * ξ ^ 2) with hα
  have hα2 : 2 < α := by
    rw [hα, lt_div_iff₀ (by positivity)]
    have : 2 * ξ < ξ * Q γ - s := by nlinarith
    nlinarith
  set β := (α - 2) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 0 + 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hKR : K ⊆ Metric.closedBall 0 (max R₀ 0) :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨ε₀, hε₀, H⟩ := h19 γ hγ hγ2 D c hD (Metric.closedBall 0 (R + 1))
    (isCompact_closedBall 0 _) s hs0 (by nlinarith) β hβ0
  set q := (1 - ((1 : ℝ) / 2) ^ s) / 2 with hq
  have hr1 : ((1 : ℝ) / 2) ^ s < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs0
  have hq0 : 0 < q := by rw [hq]; linarith
  set ε₂ := q ^ (1 / (s - χ)) with hε₂
  have hε₂0 : 0 < ε₂ := Real.rpow_pos_of_pos hq0 _
  refine ⟨β, hβ0, (2 * R / 1 + 1) ^ 2 / (1 - (1 / 2 : ℝ) ^ β), min (min ε₀ 1) ε₂,
    lt_min (lt_min hε₀ one_pos) hε₂0, ?_⟩
  intro Ω _ P _ h hh ε hε 𝕣 h𝕣
  have hε0 : 0 < ε := hε.1
  have hεε₀ : ε < ε₀ := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hεs : ε ^ (s - χ) ≤ q := by
    have h1 : ε ≤ ε₂ := (hε.2.trans_le (min_le_right _ _)).le
    calc ε ^ (s - χ) ≤ ε₂ ^ (s - χ) := Real.rpow_le_rpow hε0.le h1 (by linarith)
      _ = q := by
          rw [hε₂, ← Real.rpow_mul hq0.le, one_div_mul_cancel (by linarith), Real.rpow_one]
  set B : ℕ → ℤ × ℤ → Set Ω := fun ℓ a => (h ⁻¹' {g : DistC |
      internalDiam (D g) (sqCentred (ε * (1 / 2) ^ ℓ * 𝕣)
          (gridPt (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) a + ((ε * (1 / 2) ^ ℓ * 𝕣 / 2 : ℝ) : ℂ) * (1 + I)))
        (sqCentred (ε * (1 / 2) ^ ℓ * 𝕣)
          (gridPt (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) a + ((ε * (1 / 2) ^ ℓ * 𝕣 / 2 : ℝ) : ℂ) * (1 + I))) ≤
        ENNReal.ofReal ((ε * (1 / 2) ^ ℓ) ^ s * scaleFac ξ c g 𝕣 0)})ᶜ with hB
  have hsub : (h ⁻¹' {g : DistC |
        ∀ (k : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m ∩ scaleSet 𝕣 0 K).Nonempty →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-ξ * circleAvg g 𝕣 0)) *
              internalDiam (D g) (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m)
                (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m) ≤
            ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k * ε) ^ χ)})ᶜ ⊆
      ⋃ ℓ, ⋃ a ∈ gridSel (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) (R * 𝕣), B ℓ a := by
    intro ω hω
    by_contra hnot
    apply hω
    simp only [mem_iUnion, not_exists, hB, mem_compl_iff, not_not, mem_preimage,
      mem_ofPred_eq] at hnot
    intro k m hm
    have hF : 0 < scaleFac ξ c (h ω) 𝕣 0 :=
      mul_pos (hD.tightness.1 𝕣 h𝕣) (Real.exp_pos _)
    rw [factor_eq]
    refine sq_display_det (D (h ω)) (R := R) hF h𝕣 hε0 hε1 hs0 hχs hεs ?_ ?_ k m hm
    · intro w hw
      have := norm_le_of_mem_scaleSet h𝕣 hKR hw
      rw [hR]; nlinarith
    · intro ℓ a ha
      have := hnot ℓ a ha
      rwa [sqCentred_eq_osq (by positivity)] at this
  refine (measure_mono hsub).trans ?_
  refine grid_union_bound P (by norm_num) (by norm_num) (by norm_num) hR0 hβ0 hε0 hε1 h𝕣 B ?_
  intro ℓ a ha
  have ht0 : 0 < ε * (1 / 2 : ℝ) ^ ℓ := by positivity
  have htε : ε * (1 / 2 : ℝ) ^ ℓ < ε₀ := by
    have : (1 / 2 : ℝ) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hz : gridPt (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) a + ((ε * (1 / 2) ^ ℓ * 𝕣 / 2 : ℝ) : ℂ) * (1 + I) ∈
      scaleSet 𝕣 0 (Metric.closedBall 0 (R + 1)) := by
    refine mem_scaleSet_ball h𝕣 ?_
    have h1 : ‖gridPt (1 * (ε * (1 / 2) ^ ℓ) * 𝕣) a‖ ≤ R * 𝕣 := ha
    have h2 : ‖((ε * (1 / 2) ^ ℓ * 𝕣 / 2 : ℝ) : ℂ) * (1 + I)‖ ≤ 𝕣 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have hI : ‖(1 : ℂ) + I‖ ≤ 2 := (norm_add_le _ _).trans (by simp; norm_num)
      have : ε * (1 / 2 : ℝ) ^ ℓ ≤ 1 := by
        have : (1 / 2 : ℝ) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      calc ε * (1 / 2) ^ ℓ * 𝕣 / 2 * ‖(1 : ℂ) + I‖ ≤ ε * (1 / 2) ^ ℓ * 𝕣 / 2 * 2 := by gcongr
        _ ≤ 𝕣 := by nlinarith
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ R * 𝕣 + 𝕣 := add_le_add h1 h2
      _ = (R + 1) * 𝕣 := by ring
  have := H P h hh (ε * (1 / 2) ^ ℓ) ⟨ht0, htε⟩ 𝕣 h𝕣 _ hz
  rw [show α - β = β + 2 by rw [hβ]; ring] at this
  exact this

end L320

/-- **DFGPS Lemma 3.20** (`Blueprint.DFGPSLem3_20`) from Lemma 3.19 (ball and square parts) -/
theorem dfgpsLem3_20_of (h19 : Lem3_19U) (h19sq : Lem3_19SqU) : Blueprint.DFGPSLem3_20 :=
  fun γ hγ hγ2 D c hD K hK χ hχ hχQ =>
    ⟨L320.lem3_20_ball_of h19 γ hγ hγ2 D c hD K hK χ hχ hχQ,
      L320.lem3_20_sq_of h19sq γ hγ hγ2 D c hD K hK χ hχ hχQ⟩

end LQGMetric.DFGPS

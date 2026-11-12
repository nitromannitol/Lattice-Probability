/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_22Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_22

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.22 (`Blueprint.DFGPSLem3_22`) from Lemma 3.21 (task P2-DFA7)

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.22 (T:2367–2373), proof
T:2375–2377: the cross-distance estimate of Lemma 3.21 at the scales `t_k` and a union bound over
grid points and `k` (`grid_union_bound`); geometry in `L3_22.lean`. Axiom I (`D_h` is a length
metric a.s.) is used for the crossing argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L322

open Blueprint LQGDimension.LFPPRecords L320

/-- **DFGPS Lemma 3.22** (corrected form `Blueprint.DFGPSLem3_22`) from Lemma 3.21 -/
theorem dfgpsLem3_22_of (h21 : Lem3_21U) : DFGPSLem3_22 := by
  intro γ hγ hγ2 D c hD K hK χ' hχ'
  have hξ : 0 < xiGamma γ := DG.xiGamma_pos hγ
  set ξ := xiGamma γ with hξ_def
  have hQ : 0 < Q γ := by unfold Q; positivity
  set s := (ξ * (Q γ + 2) + χ') / 2 with hs_def
  have hs1 : ξ * (Q γ + 2) < s := by rw [hs_def]; linarith
  have hsχ : s < χ' := by rw [hs_def]; linarith
  have hs0 : 0 < s := by nlinarith
  set α := (s - ξ * Q γ) ^ 2 / (2 * ξ ^ 2) with hα
  have hα2 : 2 < α := by
    rw [hα, lt_div_iff₀ (by positivity)]
    have : 2 * ξ < s - ξ * Q γ := by nlinarith
    nlinarith
  set β := (α - 2) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 0 + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hKR : K ⊆ Metric.closedBall 0 (max R₀ 0) :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨ε₀, hε₀, H⟩ := h21 γ hγ hγ2 D c hD (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
    s (by nlinarith) β hβ0
  set ε₂ := (15 / 41 : ℝ) ^ (s / (χ' - s)) with hε₂
  have hε₂0 : 0 < ε₂ := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨β, hβ0, (2 * R / (1 / 40) + 1) ^ 2 / (1 - (3 / 4 : ℝ) ^ β), min (min ε₀ 1) ε₂,
    lt_min (lt_min hε₀ one_pos) hε₂0, ?_⟩
  intro Ω _ P _ h hh ε hε 𝕣 h𝕣
  have hε0 : 0 < ε := hε.1
  have hεε₀ : ε < ε₀ := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hεs : ε ^ (χ' - s) ≤ (15 / 41 : ℝ) ^ s := by
    have h1 : ε ≤ ε₂ := (hε.2.trans_le (min_le_right _ _)).le
    calc ε ^ (χ' - s) ≤ ε₂ ^ (χ' - s) := Real.rpow_le_rpow hε0.le h1 (by linarith)
      _ = (15 / 41 : ℝ) ^ s := by
          rw [hε₂, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (by linarith)]
  set B : ℕ → ℤ × ℤ → Set Ω := fun k a => (h ⁻¹' {g : DistC |
      ENNReal.ofReal ((ε * (3 / 4) ^ k) ^ s * scaleFac ξ c g 𝕣 0) ≤
        setDist (D g) (Metric.ball (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a)
          ((ε * (3 / 4) ^ k) * 𝕣))
        (Metric.sphere (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a)
          (2 * (ε * (3 / 4) ^ k) * 𝕣))})ᶜ with hB
  have hsub : (h ⁻¹' {g : DistC |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, ‖u - v‖ ≤ ε * 𝕣 →
          ‖(u - v) / 𝕣‖ ^ χ' ≤
            (c 𝕣)⁻¹ * Real.exp (-ξ * circleAvg g 𝕣 0) * (D g).1 (u, v)})ᶜ ⊆
      (⋃ k, ⋃ a ∈ gridSel ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) (R * 𝕣), B k a) ∪
        {ω | ¬ (D (h ω)).IsLength} := by
    intro ω hω
    by_contra hnot
    rw [mem_union, not_or] at hnot
    obtain ⟨hnot, hlen⟩ := hnot
    simp only [mem_ofPred_eq, not_not] at hlen
    apply hω
    simp only [mem_iUnion, not_exists, hB, mem_compl_iff, not_not, mem_preimage,
      mem_ofPred_eq] at hnot
    intro u hu v hv hd
    have hF : 0 < scaleFac ξ c (h ω) 𝕣 0 :=
      mul_pos (hD.tightness.1 𝕣 h𝕣) (Real.exp_pos _)
    rw [factor_eq]
    refine cross_det (D (h ω)) hlen hF h𝕣 hε0 hs0 hsχ hεs hd ?_ hnot
    have := norm_le_of_mem_scaleSet h𝕣 hKR hu
    rw [hR]; nlinarith
  have hN : P {ω | ¬ (D (h ω)).IsLength} = 0 :=
    ae_iff.1 (hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh.1))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hN, add_zero]
  refine grid_union_bound P (by norm_num) (by norm_num) (by norm_num) hR0 hβ0 hε0 hε1 h𝕣 B ?_
  intro k a ha
  have ht0 : 0 < ε * (3 / 4 : ℝ) ^ k := by positivity
  have htε : ε * (3 / 4 : ℝ) ^ k < ε₀ := by
    have : (3 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hz := mem_scaleSet_ball h𝕣 (show ‖gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a‖ ≤ R * 𝕣
    from ha)
  have := H P h hh (ε * (3 / 4) ^ k) ⟨ht0, htε⟩ 𝕣 h𝕣 _ hz
  rw [show α - β = β + 2 by rw [hβ]; ring] at this
  exact this

end L322
end LQGMetric.DFGPS

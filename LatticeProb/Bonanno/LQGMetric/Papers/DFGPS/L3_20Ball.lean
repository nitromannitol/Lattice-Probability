/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_20Ball at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_20
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Lemma 3.20 (T:2317–2322), proof
T:2327–2329: Lemma 3.19 (`eqn-ep-diam`) with `s = χ` at the scales `t_k` and the union bound
over grid points and `k`. The exponent of L3.19 is `(ξQ − χ)²/(2ξ²) > 2` exactly because
`χ < ξ(Q − 2)`; with `ζ = (α − 2)/2` the union bound gives `O(ε^{(α−2)/2})`.
Geometry and scale choice: `L3_20.lean` (DFA7-1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L320

open Blueprint LQGDimension.LFPPRecords

/-- the first display of `Blueprint.DFGPSLem3_20` (`eqn-holder-upper`) -/
def Lem3_20Ball : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (K : Set ℂ), IsCompact K → ∀ χ : ℝ, 0 < χ → χ < xiGamma γ * (Q γ - 2) →
      PolyHighProbU (fun ε 𝕣 => {g : DistC |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, u ≠ v → ‖u - v‖ ≤ ε * 𝕣 →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0)) *
              (D g).internal (Metric.ball u (2 * ‖u - v‖)) u v ≤
            ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ χ)})

lemma factor_eq (ξ : ℝ) (c : ℝ → ℝ) (g : DistC) (𝕣 : ℝ) :
    (c 𝕣)⁻¹ * Real.exp (-ξ * circleAvg g 𝕣 0) = (scaleFac ξ c g 𝕣 0)⁻¹ := by
  rw [scaleFac, mul_inv, neg_mul, Real.exp_neg]

lemma mem_scaleSet_ball {𝕣 R : ℝ} (h𝕣 : 0 < 𝕣) {z : ℂ} (hz : ‖z‖ ≤ R * 𝕣) :
    z ∈ scaleSet 𝕣 0 (Metric.closedBall 0 R) := by
  refine ⟨z / 𝕣, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣,
      div_le_iff₀ h𝕣]
    exact hz
  · have : (𝕣 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h𝕣.ne'
    field_simp; ring

lemma norm_le_of_mem_scaleSet {𝕣 R₀ : ℝ} (h𝕣 : 0 < 𝕣) {K : Set ℂ}
    (hK : K ⊆ Metric.closedBall 0 R₀) {u : ℂ} (hu : u ∈ scaleSet 𝕣 0 K) : ‖u‖ ≤ R₀ * 𝕣 := by
  obtain ⟨x, hx, rfl⟩ := hu
  have := mem_closedBall_zero_iff.1 (hK hx)
  show ‖(𝕣 : ℂ) * x + 0‖ ≤ R₀ * 𝕣
  rw [add_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣]
  nlinarith

/-- **DFGPS Lemma 3.20, first display**, from Lemma 3.19 (`eqn-ep-diam`) -/
theorem lem3_20_ball_of (h19 : Lem3_19U) : Lem3_20Ball := by
  intro γ hγ hγ2 D c hD K hK χ hχ hχQ
  have hξ : 0 < xiGamma γ := DG.xiGamma_pos hγ
  set ξ := xiGamma γ with hξ_def
  set α := (ξ * Q γ - χ) ^ 2 / (2 * ξ ^ 2) with hα
  have hα2 : 2 < α := by
    rw [hα, lt_div_iff₀ (by positivity)]
    have : 2 * ξ < ξ * Q γ - χ := by nlinarith
    nlinarith
  set β := (α - 2) / 2 with hβ
  have hβ0 : 0 < β := by rw [hβ]; linarith
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 0 + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hKR : K ⊆ Metric.closedBall 0 (max R₀ 0) :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨ε₀, hε₀, H⟩ := h19 γ hγ hγ2 D c hD (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
    χ hχ (by nlinarith) β hβ0
  refine ⟨β, hβ0, (2 * R / (1 / 40) + 1) ^ 2 / (1 - (3 / 4 : ℝ) ^ β), min ε₀ 1,
    lt_min hε₀ one_pos, ?_⟩
  intro Ω _ P _ h hh ε hε 𝕣 h𝕣
  have hε0 : 0 < ε := hε.1
  have hεε₀ : ε < ε₀ := hε.2.trans_le (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hε.2.trans_le (min_le_right _ _)).le
  set B : ℕ → ℤ × ℤ → Set Ω := fun k a => (h ⁻¹' {g : DistC |
      internalDiam (D g) (Metric.ball (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a)
          ((ε * (3 / 4) ^ k) * 𝕣))
        (Metric.ball (gridPt ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) a) (2 * (ε * (3 / 4) ^ k) * 𝕣)) ≤
        ENNReal.ofReal ((ε * (3 / 4) ^ k) ^ χ * scaleFac ξ c g 𝕣 0)})ᶜ with hB
  have hsub : (h ⁻¹' {g : DistC |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, u ≠ v → ‖u - v‖ ≤ ε * 𝕣 →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-ξ * circleAvg g 𝕣 0)) *
              (D g).internal (Metric.ball u (2 * ‖u - v‖)) u v ≤
            ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ χ)})ᶜ ⊆
      ⋃ k, ⋃ a ∈ gridSel ((1 / 40) * (ε * (3 / 4) ^ k) * 𝕣) (R * 𝕣), B k a := by
    intro ω hω
    by_contra hnot
    apply hω
    simp only [mem_iUnion, not_exists, hB, mem_compl_iff, not_not, mem_preimage,
      mem_ofPred_eq] at hnot
    intro u hu v hv huv hd
    have hF : 0 < scaleFac ξ c (h ω) 𝕣 0 :=
      mul_pos (hD.tightness.1 𝕣 h𝕣) (Real.exp_pos _)
    rw [factor_eq]
    refine ball_det (D (h ω)) hF h𝕣 hε0 hχ huv hd ?_ hnot
    have := norm_le_of_mem_scaleSet h𝕣 hKR hu
    rw [hR]; nlinarith
  refine (measure_mono hsub).trans ?_
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

end L320
end LQGMetric.DFGPS

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6P28Wire at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Low2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11Wire
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Wire

/-!
# DDDF Prop 28 for the family `δ ∈ (0,1)`: assembly of the two steps (task P2-DDDF6f)

DDDF = arXiv:1904.08021, `tightness.tex` l. 1385–1490 (+ l. 1648). DDDF split each of
(UpperHolder), (LowerHolder) by a union bound into small pairs (Step 2; here `|x − x'| ≤ δ`,
proved: `S6P28.upper_small`, `S6P28.lower_small`) and the dyadic annuli (Step 1; here
`|x − x'| > δ`, the open statements `S6UpperStep1`, `S6LowerStep1`, DDDF l. 1414–1436 and
l. 1455–1472). `upperHolderD_of_step1`, `lowerHolderD_of_step1` do the union bound, and
`dddfThm1_1_of_step1` feeds `S6Thm.dddfThm1_1_of_holder`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace LQGMetric
namespace DDDF
namespace S6P28

open WhiteNoise Blueprint

variable {Ω : Type} [MeasurableSpace Ω]

/-- **DDDF Prop 28 Part 1 Step 1 for the family** (l. 1414–1436, 1648): pairs at distance
`> δ` (the annuli `2^{-k} ≤ |x − x'| ≤ 2^{-k+1}`, `2^{-k} > δ`). Open. -/
def S6UpperStep1 (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ x y : closedUnitSquare, δ < ‖(x : ℂ) - y‖ ∧ C * ‖(x : ℂ) - y‖ ^ β <
      (lambdaDelta ξ W P δ)⁻¹ * lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y}
      ≤ ENNReal.ofReal ε

/-- **DDDF Prop 28 Part 2 Step 1 for the family** (l. 1455–1472, 1648): pairs at distance
`> δ`. Open. -/
def S6LowerStep1 (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ Ioo (0 : ℝ) 1,
    P {ω | ∃ x y : closedUnitSquare, δ < ‖(x : ℂ) - y‖ ∧ (lambdaDelta ξ W P δ)⁻¹ *
      lenMetricOn ξ (fun z => phiVer W P δ 1 z ω) closedUnitSquare x y < c * ‖(x : ℂ) - y‖ ^ α}
      ≤ ENNReal.ofReal ε

lemma half_add_half (ε : ℝ) (hε : 0 < ε) :
    ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

/-- (UpperHolder) for the family from Step 1 and Step 2 (union bound, DDDF l. 1405–1410). -/
theorem upperHolderD_of_step1 {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ q : ℝ} (hξ : 0 < ξ) (h554 : S6Eq5_54 ξ q W P) (h698 : S6Eq6_98 ξ W P) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hβ : β < ξ * (q - 2)) (h1 : S6UpperStep1 ξ W P β) :
    S6Thm.S6UpperHolderD ξ W P β := by
  intro ε hε
  obtain ⟨C1, hC1⟩ := upper_small hW hξ h554 h698 hβ0 hβ1 hβ (ε / 2) (by positivity)
  obtain ⟨C2, hC2⟩ := h1 (ε / 2) (by positivity)
  refine ⟨max C1 C2, fun δ hδ => ?_⟩
  refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans
    ((add_le_add (hC1 δ hδ) (hC2 δ hδ)).trans_eq (half_add_half ε hε)))
  rintro ω ⟨x, y, h⟩
  have hp : 0 ≤ ‖(x : ℂ) - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hxy : ‖(x : ℂ) - y‖ ≤ δ
  · exact Or.inl ⟨x, y, hxy, lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hp) h⟩
  · exact Or.inr ⟨x, y, not_le.1 hxy, lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hp) h⟩

/-- (LowerHolder) for the family from Step 1 and Step 2 (union bound, DDDF l. 1455–1463). -/
theorem lowerHolderD_of_step1 {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ q : ℝ} (hξ : 0 < ξ) (h578 : S6Eq5_78 ξ q W P) (h698 : S6Eq6_98 ξ W P) {α : ℝ}
    (hα1 : 1 ≤ α) (hα : ξ * (q + 2) < α) (h1 : S6LowerStep1 ξ W P α) :
    S6Thm.S6LowerHolderD ξ W P α := by
  intro ε hε
  obtain ⟨c1, hc1, hC1⟩ := lower_small hW hξ h578 h698 hα1 hα (ε / 2) (by positivity)
  obtain ⟨c2, hc2, hC2⟩ := h1 (ε / 2) (by positivity)
  refine ⟨min c1 c2, lt_min hc1 hc2, fun δ hδ => ?_⟩
  refine le_trans (measure_mono ?_) ((measure_union_le _ _).trans
    ((add_le_add (hC1 δ hδ) (hC2 δ hδ)).trans_eq (half_add_half ε hε)))
  rintro ω ⟨x, y, h⟩
  have hp : 0 ≤ ‖(x : ℂ) - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hxy : ‖(x : ℂ) - y‖ ≤ δ
  · exact Or.inl ⟨x, y, hxy, lt_of_lt_of_le h
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hp)⟩
  · exact Or.inr ⟨x, y, not_le.1 hxy, lt_of_lt_of_le h
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hp)⟩

/-- **DDDF Theorem 1 (1)** from (5.54), (5.78) and the two Step-1 statements of Prop 28 for the
family `δ ∈ (0,1)`. -/
theorem dddfThm1_1_of_step1
    (h : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W P ∧ S6Eq5_78 (xiGamma γ) (LQGMetric.Q γ) W P ∧
      (∀ β : ℝ, 0 < β → β < xiGamma γ * (LQGMetric.Q γ - 2) →
        S6UpperStep1 (xiGamma γ) W P β) ∧
      (∀ α : ℝ, xiGamma γ * (LQGMetric.Q γ + 2) < α → S6LowerStep1 (xiGamma γ) W P α)) :
    Blueprint.DDDFThm1_1 := by
  refine S6Thm.dddfThm1_1_of_holder fun γ hγ hγ2 Ω _ P W hW => ?_
  obtain ⟨h554, h578, hU, hL⟩ := h γ hγ hγ2 P W hW
  have h698 := s6_eq6_98_of_554 hγ hγ2 hW h554
  have hξ := xiGamma_pos' hγ
  have hQ := S6D.two_lt_Q' hγ hγ2
  have hpos : 0 < xiGamma γ * (LQGMetric.Q γ - 2) := mul_pos hξ (by linarith)
  set β := min (1 / 2) (xiGamma γ * (LQGMetric.Q γ - 2) / 2) with hβ_def
  have hβ0 : 0 < β := lt_min (by norm_num) (by positivity)
  have hβ1 : β ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hβ : β < xiGamma γ * (LQGMetric.Q γ - 2) := (min_le_right _ _).trans_lt (by linarith)
  set α := max 1 (xiGamma γ * (LQGMetric.Q γ + 2) + 1) with hα_def
  have hα1 : 1 ≤ α := le_max_left _ _
  have hα : xiGamma γ * (LQGMetric.Q γ + 2) < α :=
    (lt_add_one _).trans_le (le_max_right _ _)
  exact ⟨h554, α, β, by linarith, hβ0,
    upperHolderD_of_step1 hW hξ h554 h698 hβ0 hβ1 hβ (hU β hβ0 hβ),
    lowerHolderD_of_step1 hW hξ h578 h698 hα1 hα (hL α hα)⟩

end S6P28
end DDDF
end LQGMetric

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.FiniteBoxesLowerTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.GaussianTwoSum

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem perc_field_finite_boxes_lower_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (ρ : ℝ) (hρ : 0 < ρ) (F : Finset ℂ) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
        let r : ℝ := (2 : ℝ)⁻¹ ^ k
        P {ω | (⨅ c ∈ F, scaledBoxCrossMin (ξ : ℝ)
            (fun z => phiMN W P 0 n z ω) c ρ r) <
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
            ENNReal.ofReal (T⁻¹ *
              ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))} ≤
          ENNReal.ofReal (c₀ * Real.exp (-c₁ * (Real.log T) ^ 2)) := by
  induction F using Finset.induction_on with
  | empty =>
      refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
      intro Ω _ P _ W _ n k _ T _
      simp
  | @insert c F hc ih =>
      obtain ⟨a₀, b₀, ha₀, hb₀, hbox⟩ :=
        perc_field_one_box_lower_of_inputs hPerc hExp ξ Q hQ ζ hζ c ρ hρ
      obtain ⟨a₁, b₁, ha₁, hb₁, hrest⟩ := ih
      refine ⟨a₀ + a₁, min b₀ b₁, by positivity,
        lt_min hb₀ hb₁, ?_⟩
      intro Ω _ P _ W hW n k hkn T hT
      let r : ℝ := (2 : ℝ)⁻¹ ^ k
      let threshold : Ω → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * phiMN W P 0 k 0 ω)) *
          ENNReal.ofReal (T⁻¹ *
            ((2 : ℝ) ^ (-((ξ : ℝ) * Q + ζ) * (k : ℝ)) * lambdaN ξ W P n))
      have h₀ := hbox P W hW n k hkn T hT
      have h₁ := hrest P W hW n k hkn T hT
      have hsub :
          {ω | (⨅ d ∈ insert c F, scaledBoxCrossMin (ξ : ℝ)
              (fun z => phiMN W P 0 n z ω) d ρ r) < threshold ω} ⊆
            {ω | scaledBoxCrossMin (ξ : ℝ)
              (fun z => phiMN W P 0 n z ω) c ρ r < threshold ω} ∪
            {ω | (⨅ d ∈ F, scaledBoxCrossMin (ξ : ℝ)
              (fun z => phiMN W P 0 n z ω) d ρ r) < threshold ω} := by
        intro ω hω
        simpa only [Finset.iInf_insert, inf_lt_iff,
          mem_ofPred_eq, mem_union] using hω
      calc
        P {ω | (⨅ d ∈ insert c F, scaledBoxCrossMin (ξ : ℝ)
            (fun z => phiMN W P 0 n z ω) d ρ r) < threshold ω} ≤
          P ({ω | scaledBoxCrossMin (ξ : ℝ)
              (fun z => phiMN W P 0 n z ω) c ρ r < threshold ω} ∪
            {ω | (⨅ d ∈ F, scaledBoxCrossMin (ξ : ℝ)
              (fun z => phiMN W P 0 n z ω) d ρ r) < threshold ω}) :=
            measure_mono hsub
        _ ≤ P {ω | scaledBoxCrossMin (ξ : ℝ)
              (fun z => phiMN W P 0 n z ω) c ρ r < threshold ω} +
            P {ω | (⨅ d ∈ F, scaledBoxCrossMin (ξ : ℝ)
              (fun z => phiMN W P 0 n z ω) d ρ r) < threshold ω} :=
            measure_union_le _ _
        _ ≤ ENNReal.ofReal (a₀ * Real.exp (-b₀ * (Real.log T) ^ 2)) +
            ENNReal.ofReal (a₁ * Real.exp (-b₁ * (Real.log T) ^ 2)) := by
              exact add_le_add (by simpa only [r, threshold] using h₀)
                (by simpa only [r, threshold] using h₁)
        _ ≤ ENNReal.ofReal ((a₀ + a₁) *
            Real.exp (-(min b₀ b₁) * (Real.log T) ^ 2)) :=
              gaussian_two_sum_bound a₀ a₁ b₀ b₁ T ha₀ ha₁

end SupercriticalLQGUniqueness.B2.DG20Pt


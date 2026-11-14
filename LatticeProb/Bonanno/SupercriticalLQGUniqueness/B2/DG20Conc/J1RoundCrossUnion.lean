/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundCrossUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundCrossPoint
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockCountRadius

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

theorem j1_source_round_cross_union
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ CN cN : ℝ, 24 ≤ R₀ ∧ 0 < CN ∧ 0 < cN ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n m : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hmK : m ≤ K) (hR : R₀ ≤ (2 : ℝ)^m)
        (hRK : (2 : ℝ)^m ≤ 2 * (K : ℝ))
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ)
        (hT : Real.exp (6 * (C + 1) *
          Real.sqrt ((K : ℝ) + 1)) ≤ T),
        P {ω | ∃ b ∈ T20B.nearIdx K,
          crossLenIn ξ (fun z => phiMN W P K n z ω)
            (j1SourceCross K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b) <
            ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) := by
  obtain ⟨R₀, CN, cN, hR₀, hCN, hcN, hpoint⟩ :=
    j1_source_round_cross_pointwise hunit hp hpHalf C hC
  refine ⟨R₀, CN, cN, hR₀, hCN, hcN, ?_⟩
  intro Ω _ P W hW K n m hK hKn hmK hR hRK hH T hT
  let E : ℤ × ℤ → Set Ω := fun b =>
    {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (j1SourceCross K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b) <
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))}
  have hblock : ∀ b ∈ T20B.nearIdx K,
      P (E b) ≤ ENNReal.ofReal (CN * (2 : ℝ)^m *
        Real.exp (-cN * (Real.log T)^2)) := by
    intro b hb
    exact hpoint P W hW K n m hKn hmK hR hH b T hT
  have hsum :
      P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} ≤
      ((T20B.nearIdx K).card : ℝ≥0∞) *
        ENNReal.ofReal (CN * (2 : ℝ)^m *
          Real.exp (-cN * (Real.log T)^2)) := by
    calc
      P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} =
          P (⋃ b ∈ T20B.nearIdx K, E b) := by
            congr 1; ext ω; simp
      _ ≤ ((T20B.nearIdx K).card : ℝ≥0∞) *
          ENNReal.ofReal (CN * (2 : ℝ)^m *
            Real.exp (-cN * (Real.log T)^2)) := by
            refine (measure_biUnion_finset_le (T20B.nearIdx K) E).trans ?_
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            exact Finset.sum_le_sum fun b hb => hblock b hb
  have hcoeff := j1_nearIdx_card_radius_le_five K hK
    ((2 : ℝ)^m) (by positivity) hRK
  have hq0 : 0 ≤ CN * Real.exp (-cN * (Real.log T)^2) := by positivity
  calc
    P {ω | ∃ b ∈ T20B.nearIdx K,
      crossLenIn ξ (fun z => phiMN W P K n z ω)
        (j1SourceCross K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b) <
        ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} =
        P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} := by rfl
    _ ≤ ((T20B.nearIdx K).card : ℝ≥0∞) *
      ENNReal.ofReal (CN * (2 : ℝ)^m *
        Real.exp (-cN * (Real.log T)^2)) := hsum
    _ = ENNReal.ofReal (((T20B.nearIdx K).card : ℝ) *
        (2 : ℝ)^m) *
        ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) := by
          conv_lhs =>
            rw [← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (by positivity :
                0 ≤ ((T20B.nearIdx K).card : ℝ))]
          conv_rhs =>
            rw [← ENNReal.ofReal_mul (by positivity :
              0 ≤ ((T20B.nearIdx K).card : ℝ) * (2 : ℝ)^m)]
          congr 1
          ring
    _ ≤ ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoeff)
            (zero_le : (0 : ℝ≥0∞) ≤ _)

end SupercriticalLQGUniqueness.B2.DG20Conc

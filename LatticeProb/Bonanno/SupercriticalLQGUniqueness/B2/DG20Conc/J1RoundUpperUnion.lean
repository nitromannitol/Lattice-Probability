/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperPhysicalPoint
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockCountRadius

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_source_round_upper_union
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ A CP cP : ℝ,
      24 ≤ R₀ ∧ 0 < A ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n m : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n) (hmK : m ≤ K)
        (hR : R₀ ≤ (2 : ℝ)^m)
        (hRK : (2 : ℝ)^m ≤ 2 * (K : ℝ))
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ)
        (hT : Real.exp (A * Real.sqrt ((K : ℝ) + 1)) ≤ T),
        P {ω | ∃ b ∈ T20B.nearIdx K,
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
          (lfppContMetric ξ (fun z => phiMN W P K n z ω)
            ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
            (LaneCInputs.sourceAround K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨R₀, A, CP, cP, hR₀, hA, hCP, hcP, hpoint⟩ :=
    j1_source_round_upper_pointwise hunit hp hpHalf C hC
  refine ⟨R₀, A, CP, cP, hR₀, hA, hCP, hcP, ?_⟩
  intro Ω _ P W hW K n m hK hKn hmK hR hRK hH T hT
  let E : ℤ × ℤ → Set Ω := fun b =>
    {ω | ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
      ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
      (lfppContMetric ξ (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)}
  have hblock : ∀ b ∈ T20B.nearIdx K,
      P (E b) ≤ ENNReal.ofReal (CP * (2 : ℝ)^m *
        Real.exp (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
    intro b hb
    exact hpoint P W hW K n m hKn hmK hR hRK hH b T hT
  have hsum :
      P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} ≤
      ((T20B.nearIdx K).card : ℝ≥0∞) *
        ENNReal.ofReal (CP * (2 : ℝ)^m *
          Real.exp (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
    calc
      P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} =
          P (⋃ b ∈ T20B.nearIdx K, E b) := by
            congr 1; ext ω; simp
      _ ≤ ((T20B.nearIdx K).card : ℝ≥0∞) *
          ENNReal.ofReal (CP * (2 : ℝ)^m *
            Real.exp (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
            refine (measure_biUnion_finset_le (T20B.nearIdx K) E).trans ?_
            rw [← nsmul_eq_mul, ← Finset.sum_const]
            exact Finset.sum_le_sum fun b hb => hblock b hb
  have hcoeff := j1_nearIdx_card_radius_le_five K hK
    ((2 : ℝ)^m) (by positivity) hRK
  have hq0 : 0 ≤ CP * Real.exp
      (-cP * (Real.log T)^2 / Real.log (Real.log T)) := by positivity
  calc
    P {ω | ∃ b ∈ T20B.nearIdx K,
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
        ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
      (lfppContMetric ξ (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)} =
        P {ω | ∃ b ∈ T20B.nearIdx K, ω ∈ E b} := by rfl
    _ ≤ ((T20B.nearIdx K).card : ℝ≥0∞) *
      ENNReal.ofReal (CP * (2 : ℝ)^m *
        Real.exp (-cP * (Real.log T)^2 / Real.log (Real.log T))) := hsum
    _ = ENNReal.ofReal (((T20B.nearIdx K).card : ℝ) *
        (2 : ℝ)^m) *
        ENNReal.ofReal (CP * Real.exp
          (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
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
        ENNReal.ofReal (CP * Real.exp
          (-cP * (Real.log T)^2 / Real.log (Real.log T))) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcoeff)
            (zero_le : (0 : ℝ≥0∞) ≤ _)

end SupercriticalLQGUniqueness.B2.DG20Conc

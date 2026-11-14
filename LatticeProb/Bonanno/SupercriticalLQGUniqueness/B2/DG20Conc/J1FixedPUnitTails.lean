/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPUnitTails at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1ThresholdShift
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPHigh
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUnitGeometry

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_fixed_p_unit_tails_of_induction
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C), ∃ A₀ CN cN CP cP : ℝ,
      0 < A₀ ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K m : ℕ)
        (hH : LambdaN ξ W P m (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (c : ℂ) (T : ℝ)
        (hT : Real.exp ((A₀ + 5) * (C + 1) *
          Real.sqrt ((K : ℝ) + 1)) ≤ T),
        let B := Real.exp (C * Real.sqrt (K : ℝ))
        P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P m)} ≤
          ENNReal.ofReal (CN * Real.exp
            (-cN * (Real.log (T / B))^2)) ∧
        P {ω | ENNReal.ofReal (T * lambdaN ξ W P m) <
          (lfppContMetric ξ (fun z => phiMN W P K (K + m)
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
            ((isPhiVersion_phiMN hW (by omega : K ≤ K + m)).cont ω |>.comp
              (show Continuous (fun z : ℂ =>
                (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal (CP * Real.exp
            (-cP * (Real.log (T / B))^2 /
              Real.log (Real.log (T / B)))) := by
  obtain ⟨p, hp, hpHalf, hunit, hfixed⟩ :=
    j1_fixed_p_small_high_of_C1 laneC_unit_block_geometry hξ
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨A₀, CN, cN, CP, cP,
    hA₀, hCN, hcN, hCP, hcP, hA2⟩ := hfixed C hC
  refine ⟨A₀, CN, cN, CP, cP,
    hA₀, hCN, hcN, hCP, hcP, ?_⟩
  intro Ω _ P W hW K m hH i c T hT
  dsimp
  let B : ℝ := Real.exp (C * Real.sqrt (K : ℝ))
  have hB : 0 < B := Real.exp_pos _
  obtain ⟨hs, hsStart⟩ := j1_induction_parameter_shift hA₀ hC K hT
  have hT0 : 0 < T := by
    have hh : 0 < Real.exp ((A₀ + 5) * (C + 1) *
        Real.sqrt ((K : ℝ) + 1)) := Real.exp_pos _
    exact hh.trans_le hT
  obtain ⟨hmed, hupper⟩ := j1_quantile_sandwich_of_induction
    P hW ξ hp (by linarith) hH
  obtain ⟨hlow, hupp⟩ := hA2 P W hW K m hH i c (T / B) hs
  have hlow' := hlow hsStart
  have hsubL :
      {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
        (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P m)} ⊆
      {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
        (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
        ENNReal.ofReal ((T / B)⁻¹ *
          ellN ξ W P m (ENNReal.ofReal p))} := by
    intro ω hω
    exact hω.trans_le (ENNReal.ofReal_le_ofReal
      (j1_lower_threshold_of_quantile hB hT0 hmed))
  have hsubU :
      {ω | ENNReal.ofReal (T * lambdaN ξ W P m) <
        (lfppContMetric ξ (fun z => phiMN W P K (K + m)
          (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
          ((isPhiVersion_phiMN hW (by omega : K ≤ K + m)).cont ω |>.comp
            (show Continuous (fun z : ℂ =>
              (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
          (laneCUnitUaround i) (laneCUnitInner i)
          (laneCUnitOuter i)} ⊆
      {ω | ENNReal.ofReal ((T / B) *
        (LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p))) <
        (lfppContMetric ξ (fun z => phiMN W P K (K + m)
          (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
          ((isPhiVersion_phiMN hW (by omega : K ≤ K + m)).cont ω |>.comp
            (show Continuous (fun z : ℂ =>
              (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
          (laneCUnitUaround i) (laneCUnitInner i)
          (laneCUnitOuter i)} := by
    intro ω hω
    exact (ENNReal.ofReal_le_ofReal
      (j1_upper_threshold_of_quantile hB hT0 hupper)).trans_lt hω
  constructor
  · exact (measure_mono hsubL).trans hlow'
  · exact (measure_mono hsubU).trans (by
      simpa only [mul_assoc] using hupp)

end SupercriticalLQGUniqueness.B2.DG20Conc

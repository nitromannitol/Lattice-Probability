/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPUnitRate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1ShiftRate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPUnitTails

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_fixed_p_unit_source_rates
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
        P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
          ENNReal.ofReal (T⁻¹ * lambdaN ξ W P m)} ≤
          ENNReal.ofReal (CN * Real.exp
            (-cN * (Real.log T)^2)) ∧
        P {ω | ENNReal.ofReal (T * lambdaN ξ W P m) <
          (lfppContMetric ξ (fun z => phiMN W P K (K + m)
            (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c) ω)
            ((isPhiVersion_phiMN hW (by omega : K ≤ K + m)).cont ω |>.comp
              (show Continuous (fun z : ℂ =>
                (((2 : ℝ)⁻¹ ^ K : ℝ) * z + c)) by fun_prop))).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal (CP * Real.exp
            (-cP * (Real.log T)^2 /
              Real.log (Real.log T))) := by
  obtain ⟨p, hp, hpHalf, hchosen, hfixed⟩ :=
    j1_fixed_p_unit_tails_of_induction hξ
  refine ⟨p, hp, hpHalf, hchosen, ?_⟩
  intro C hC
  obtain ⟨A₀, CN, cN, CP, cP,
    hA₀, hCN, hcN, hCP, hcP, hunit⟩ := hfixed C hC
  refine ⟨A₀, CN, cN / 4, CP, cP / 4,
    hA₀, hCN, by positivity, hCP, by positivity, ?_⟩
  intro Ω _ P W hW K m hH i c T hT
  obtain ⟨hlow, hupp⟩ := hunit P W hW K m hH i c T hT
  obtain ⟨hrL, hrU⟩ :=
    j1_induction_shifted_rates hA₀ hC hcN hcP hCN.le hCP.le K hT
  constructor
  · exact hlow.trans (ENNReal.ofReal_le_ofReal hrL)
  · exact hupp.trans (ENNReal.ofReal_le_ofReal hrU)

end SupercriticalLQGUniqueness.B2.DG20Conc

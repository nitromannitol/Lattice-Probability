/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePRoundAll at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundCrossUnion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundUpperUnion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_same_p_physical_round_all
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ CN cN CP cP : ℝ,
      24 ≤ R₀ ∧ 0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n m : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hmK : m ≤ K) (hR : R₀ ≤ (2 : ℝ)^m)
        (hRK : (2 : ℝ)^m ≤ 2 * (K : ℝ))
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ) (hT : 3 < T),
        P {ω | ∃ b ∈ T20B.nearIdx K,
          crossLenIn ξ (fun z => phiMN W P K n z ω)
            (j1SourceCross K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b) <
            ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) ∧
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
  obtain ⟨Rn, CN, cN, hRn, hCN, hcN, hlow⟩ :=
    j1_source_round_cross_union hunit hp hpHalf C hC
  obtain ⟨Rp, A, CP, cP, hRp, hA, hCP, hcP, hupp⟩ :=
    j1_source_round_upper_union hunit hp hpHalf C hC
  obtain ⟨CN', cN', hCN', hcN', hlowExt⟩ :=
    j1_cross_range_extension 6 C CN cN
      (by norm_num) hC hCN hcN
  obtain ⟨CP', cP', hCP', hcP', huppExt⟩ :=
    j1_upper_range_extension A CP cP hA hCP hcP
  let R₀ := max Rn Rp
  refine ⟨R₀, CN', cN', CP', cP',
    (hRn.trans (le_max_left _ _)), hCN', hcN', hCP', hcP', ?_⟩
  intro Ω _ P W hW K n m hK hKn hmK hR hRK hH T hT
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let Es : Set Ω := {ω | ∃ b ∈ T20B.nearIdx K,
    crossLenIn ξ (fun z => phiMN W P K n z ω)
      (j1SourceCross K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b) <
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))}
  let Ea : Set Ω := {ω | ∃ b ∈ T20B.nearIdx K,
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
      ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
      (lfppContMetric ξ (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)}
  have hs : P Es ≤ ENNReal.ofReal ((5 : ℝ)^K) *
      ENNReal.ofReal (CN' * Real.exp (-cN' * (Real.log T)^2)) := by
    apply hlowExt P K hK T hT Es
    intro ht
    exact hlow P W hW K n m hK hKn hmK
      ((le_max_left Rn Rp).trans hR) hRK hH T ht
  have ha : P Ea ≤ ENNReal.ofReal ((5 : ℝ)^K) *
      ENNReal.ofReal (CP' * Real.exp
        (-cP' * (Real.log T)^2 / Real.log (Real.log T))) := by
    apply huppExt P K hK T hT Ea
    intro ht
    exact hupp P W hW K n m hK hKn hmK
      ((le_max_right Rn Rp).trans hR) hRK hH T ht
  exact ⟨hs, ha⟩

end SupercriticalLQGUniqueness.B2.DG20Conc

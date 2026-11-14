/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundFullRaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePRoundAll
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundFullUpperRaw

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_same_p_round_full_raw
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ R₀ CN cN CP cP CgN σN CgP σP : ℝ,
      24 ≤ R₀ ∧ 0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      0 < CgN ∧ 0 < σN ∧ 0 < CgP ∧ 0 < σP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n m : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hmK : m + 1 ≤ K) (hR : R₀ ≤ (2 : ℝ)^m)
        (hRK : (2 : ℝ)^m ≤ 2 * (K : ℝ))
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ) (hT : 0 < T)
        (hs : 3 < j1CoarseTailParameter ξ ((2 : ℝ)^(m+1)) T),
        let s := j1CoarseTailParameter ξ ((2 : ℝ)^(m+1)) T
        P {ω | ∃ b ∈ j1NearbyIdx K,
          ENNReal.ofReal
            (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
            crossLenIn ξ (fun z => phiMN W P 0 n z ω)
              (j1SourceCross K m b)
              (LaneCInputs.sourceInner K m b)
              (LaneCInputs.sourceOuter K m b) <
            ENNReal.ofReal
              (T⁻¹ * ((2 : ℝ)⁻¹ ^ K * lambdaN ξ W P (n-K)))} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log s)^2)) +
          ENNReal.ofReal
            (CgN * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σN))) ∧
        P {ω | ∃ b ∈ j1NearbyIdx K,
          ENNReal.ofReal (T * ((2 : ℝ)⁻¹ ^ K *
            lambdaN ξ W P (n-K))) <
            ENNReal.ofReal
              (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
              (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                (LaneCInputs.sourceAround K m b)
                (LaneCInputs.sourceInner K m b)
                (LaneCInputs.sourceOuter K m b)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log s)^2 / Real.log (Real.log s))) +
          ENNReal.ofReal
            (CgP * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σP))) := by
  obtain ⟨R₀, CN, cN, CP, cP,
    hR₀, hCN, hcN, hCP, hcP, hfine⟩ :=
      j1_same_p_physical_round_all hunit hp hpHalf C hC
  obtain ⟨CgN, σN, hCgN, hσN, hlow⟩ :=
    j1_round_full_lower_raw_of_fine_tail ξ
  obtain ⟨CgP, σP, hCgP, hσP, hupp⟩ :=
    j1_round_full_upper_raw_of_fine_tail ξ
  refine ⟨R₀, CN, cN, CP, cP, CgN, σN, CgP, σP,
    hR₀, hCN, hcN, hCP, hcP,
    hCgN, hσN, hCgP, hσP, ?_⟩
  intro Ω _ P W hW K n m hK hKn hmK hR hRK hH T hT hs
  dsimp only
  let s := j1CoarseTailParameter ξ ((2 : ℝ)^(m+1)) T
  obtain ⟨hFineLow, hFineUp⟩ :=
    hfine P W hW K n m hK hKn (by omega) hR hRK hH s hs
  constructor
  · exact hlow P W hW K n m hKn hmK T
      (lambdaN ξ W P (n-K)) hT hs
      (ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (CN * Real.exp (-cN * (Real.log s)^2)))
      hFineLow
  · exact hupp P W hW K n m hKn hmK T
      (lambdaN ξ W P (n-K)) hT hs
      (ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (CP * Real.exp
          (-cP * (Real.log s)^2 / Real.log (Real.log s))))
      hFineUp

end SupercriticalLQGUniqueness.B2.DG20Conc

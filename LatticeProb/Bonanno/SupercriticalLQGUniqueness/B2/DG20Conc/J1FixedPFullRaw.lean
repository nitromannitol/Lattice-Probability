/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPFullRaw at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallFullUpperRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPSmallAll

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_fixed_p_small_full_raw_with_fine
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C),
        ∃ CN cN CP cP CgN σN CgP σP : ℝ,
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      0 < CgN ∧ 0 < σN ∧ 0 < CgP ∧ 0 < σP ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ) (hT : 3 < T),
        P {ω | ∃ b ∈ T20B.nearIdx K,
          crossLenIn ξ (fun z => phiMN W P K n z ω)
            (laneBBlockAnnulus i (T20.dyCenter K b) K)
            (j1BlockInner i (T20.dyCenter K b) K)
            (j1BlockOuter i (T20.dyCenter K b) K) <
            ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) ∧
        P {ω | ∃ b ∈ T20B.nearIdx K,
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
            (lfppContMetric ξ (fun z => phiMN W P K n z ω)
              ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
              (laneBBlockAround i (T20.dyCenter K b) K)
              (j1BlockInner i (T20.dyCenter K b) K)
              (j1BlockOuter i (T20.dyCenter K b) K)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T)))) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ) (hT : 0 < T)
        (hs : 3 < j1CoarseTailParameter ξ 5 T),
        let s := j1CoarseTailParameter ξ 5 T
        P {ω | ∃ b ∈ j1NearbyIdx K,
          ENNReal.ofReal
            (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
            crossLenIn ξ (fun z => phiMN W P 0 n z ω)
              (laneBBlockAnnulus i (T20.dyCenter K b) K)
              (j1BlockInner i (T20.dyCenter K b) K)
              (j1BlockOuter i (T20.dyCenter K b) K) <
            ENNReal.ofReal
              (T⁻¹ * ((2 : ℝ)⁻¹ ^ K * lambdaN ξ W P (n - K)))} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log s)^2)) +
          ENNReal.ofReal
            (CgN * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σN))) ∧
        P {ω | ∃ b ∈ j1NearbyIdx K,
          ENNReal.ofReal (T * ((2 : ℝ)⁻¹ ^ K *
            lambdaN ξ W P (n - K))) <
            ENNReal.ofReal
              (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
              (lfppContMetric ξ (fun z => phiMN W P 0 n z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le n)).cont ω)).aroundDist
                (laneBBlockAround i (T20.dyCenter K b) K)
                (j1BlockInner i (T20.dyCenter K b) K)
                (j1BlockOuter i (T20.dyCenter K b) K)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log s)^2 / Real.log (Real.log s))) +
          ENNReal.ofReal
            (CgP * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σP))) := by
  obtain ⟨p, hp, hpHalf, hunit, hfixed⟩ := j1_fixed_p_physical_small_all hξ
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨CN, cN, CP, cP,
    hCN, hcN, hCP, hcP, hfine⟩ := hfixed C hC
  obtain ⟨CgN, σN, hCgN, hσN, hlow⟩ :=
    j1_small_full_lower_raw_of_fine_tail ξ
  obtain ⟨CgP, σP, hCgP, hσP, hupp⟩ :=
    j1_small_full_upper_raw_of_fine_tail ξ
  refine ⟨CN, cN, CP, cP, CgN, σN, CgP, σP,
    hCN, hcN, hCP, hcP,
    hCgN, hσN, hCgP, hσP, hfine, ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT hs
  dsimp only
  let s := j1CoarseTailParameter ξ 5 T
  obtain ⟨hFineLow, hFineUp⟩ :=
    hfine P W hW K n hK hKn hH i s hs
  constructor
  · exact hlow P W hW K n (by omega) hKn i T
      (lambdaN ξ W P (n - K)) hT hs
      (ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (CN * Real.exp (-cN * (Real.log s)^2)))
      hFineLow
  · exact hupp P W hW K n (by omega) hKn i T
      (lambdaN ξ W P (n - K)) hT hs
      (ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (CP * Real.exp
          (-cP * (Real.log s)^2 / Real.log (Real.log s))))
      hFineUp

end SupercriticalLQGUniqueness.B2.DG20Conc

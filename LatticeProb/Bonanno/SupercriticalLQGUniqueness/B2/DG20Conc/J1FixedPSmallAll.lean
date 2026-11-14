/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPSmallAll at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPPhysicalSmall
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

theorem j1_fixed_p_physical_small_all
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C), ∃ CN cN CP cP : ℝ,
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
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
              (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, hp, hpHalf, hunit, hfixed⟩ := j1_fixed_p_physical_small_high hξ
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨A, CN, cN, CP, cP,
    hA, hCN, hcN, hCP, hcP, hhigh⟩ := hfixed C hC
  let D : ℝ := (A + 5) * (C + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨CN', cN', hCN', hcN', hlowExt⟩ :=
    j1_cross_range_extension (A + 5) C CN cN
      (by linarith) hC hCN hcN
  obtain ⟨CP', cP', hCP', hcP', huppExt⟩ :=
    j1_upper_range_extension D CP cP hD hCP hcP
  refine ⟨CN', cN', CP', cP',
    hCN', hcN', hCP', hcP', ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let Es : Set Ω := {ω | ∃ b ∈ T20B.nearIdx K,
    crossLenIn ξ (fun z => phiMN W P K n z ω)
      (laneBBlockAnnulus i (T20.dyCenter K b) K)
      (j1BlockInner i (T20.dyCenter K b) K)
      (j1BlockOuter i (T20.dyCenter K b) K) <
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))}
  let Ea : Set Ω := {ω | ∃ b ∈ T20B.nearIdx K,
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
      ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
      (lfppContMetric ξ (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (laneBBlockAround i (T20.dyCenter K b) K)
        (j1BlockInner i (T20.dyCenter K b) K)
        (j1BlockOuter i (T20.dyCenter K b) K)}
  have hs : P Es ≤ ENNReal.ofReal ((5 : ℝ)^K) *
      ENNReal.ofReal (CN' * Real.exp (-cN' * (Real.log T)^2)) := by
    apply hlowExt P K hK T hT Es
    intro ht
    exact (hhigh P W hW K n hK hKn hH i T ht).1
  have ha : P Ea ≤ ENNReal.ofReal ((5 : ℝ)^K) *
      ENNReal.ofReal (CP' * Real.exp
        (-cP' * (Real.log T)^2 / Real.log (Real.log T))) := by
    apply huppExt P K hK T hT Ea
    intro ht
    exact (hhigh P W hW K n hK hKn hH i T
      (show Real.exp (D * Real.sqrt ((K : ℝ) + 1)) ≤ T from ht)).2
  exact ⟨hs, ha⟩

end SupercriticalLQGUniqueness.B2.DG20Conc

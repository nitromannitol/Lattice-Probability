/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPCutoffFine at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallFullUpperRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfNumeric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPFullHalf
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceCutoffOfFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfStartMono

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_fixed_p_small_full_half_and_cutoff_with_fine
    {ξ : ℝ} (hξ : 0 < ξ) (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
     :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C),
        ∃ CNf cNf CPf cPf CN cN CP cP : ℝ, ∃ Kfull : ℕ,
      0 < CNf ∧ 0 < cNf ∧ 0 < CPf ∧ 0 < cPf ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧ 64 ≤ Kfull ∧
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
            ENNReal.ofReal (CNf * Real.exp (-cNf * (Real.log T)^2)) ∧
        P {ω | ∃ b ∈ T20B.nearIdx K,
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
            (lfppContMetric ξ (fun z => phiMN W P K n z ω)
              ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
              (laneBBlockAround i (T20.dyCenter K b) K)
              (j1BlockInner i (T20.dyCenter K b) K)
              (j1BlockOuter i (T20.dyCenter K b) K)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CPf * Real.exp
              (-cPf * (Real.log T)^2 / Real.log (Real.log T)))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : Kfull ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : (2 : ℝ)^(((1 / 2 : ℝ) * (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) < T),
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        P {ω | ∃ b ∈ I, ω ∈ j1SmallFullLowerEvent ξ W P K n i T L b} ≤
          ENNReal.ofReal (CN * (5 : ℝ)^K * Real.exp
            (-cN * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1SmallFullUpperEvent ξ W P hW K n i T L b} ≤
          ENNReal.ofReal (CP * (5 : ℝ)^K * Real.exp
            (-cP * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) ∧
      ∃ CN' cN' CP' cP' : ℝ, ∃ Kcut : ℕ,
        0 < CN' ∧ 0 < cN' ∧ 0 < CP' ∧ 0 < cP' ∧ 64 ≤ Kcut ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : Kcut ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T),
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        P {ω | ∃ b ∈ I, ω ∈ j1SmallCutLowerEvent ξ Q W P K n i T L b} ≤
          ENNReal.ofReal (CN' * (5 : ℝ)^K * Real.exp
            (-cN' * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1SmallCutUpperEvent ξ Q W P hW K n i T L b} ≤
          ENNReal.ofReal (CP' * (5 : ℝ)^K * Real.exp
            (-cP' * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := by
  obtain ⟨p, hp, hpHalf, hunit, hfixed⟩ :=
    j1_fixed_p_small_source_full_tails_half_with_fine hξ Q hε
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨CNf, cNf, CPf, cPf, CN, cN, CP, cP, Kfull,
    hCNf, hcNf, hCPf, hcPf,
    hCN, hcN, hCP, hcP, hKfull, hfine, hfull⟩ := hfixed C hC
  obtain ⟨CN', cN', CP', cP', Kcut,
    hCN', hcN', hCP', hcP', hKcut, hcut⟩ :=
    j1_small_source_cutoff_tails_of_full hξ Q hε C hC Kfull
      hCN hcN hCP hcP hKfull hfull
  exact ⟨CNf, cNf, CPf, cPf, CN, cN, CP, cP, Kfull,
    hCNf, hcNf, hCPf, hcPf,
    hCN, hcN, hCP, hcP, hKfull, hfine, hfull,
    CN', cN', CP', cP', Kcut,
    hCN', hcN', hCP', hcP', hKcut, hcut⟩

end SupercriticalLQGUniqueness.B2.DG20Conc

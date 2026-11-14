/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPFullHalf at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallFullUpperRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPFullRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfNumeric

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_fixed_p_small_source_full_tails_half_with_fine
    {ξ : ℝ} (hξ : 0 < ξ) (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
     :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C),
        ∃ CNf cNf CPf cPf CN cN CP cP : ℝ, ∃ K₀ : ℕ,
      0 < CNf ∧ 0 < cNf ∧ 0 < CPf ∧ 0 < cPf ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      64 ≤ K₀ ∧
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
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : K₀ ≤ K) (hKn : K ≤ n)
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
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := by
  obtain ⟨p, hp, hpHalf, hunit, hfixed⟩ := j1_fixed_p_small_full_raw_with_fine hξ
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨Cn, cn, Cp, cp, Cgn, σn, Cgp, σp,
    hCn, hcn, hCp, hcp, hCgn, hσn, hCgp, hσp,
    hfine, hraw⟩ := hfixed C hC
  obtain ⟨cn₀, hcn₀, hlowRate⟩ :=
    j1_source_lower_two_rate ξ Q Cn cn Cgn σn hCn hcn hCgn hσn
  obtain ⟨cp₀, hcp₀, huppRate⟩ :=
    j1_source_upper_two_rate ξ Q Cp cp Cgp σp hCp hcp hCgp hσp
  obtain ⟨K₀, hK₀, hnum⟩ := j1_half_numeric_conditions ξ Q hε 24
  refine ⟨Cn, cn, Cp, cp, Cn + Cgn, cn₀, Cp + Cgp, cp₀, K₀,
    hCn, hcn, hCp, hcp,
    by linarith, hcn₀, by linarith, hcp₀, hK₀, hfine, ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT
  dsimp only
  have hK64 : 64 ≤ K := hK₀.trans hK
  have hK2 : 2 ≤ K := by omega
  obtain ⟨_, _, _, _, hs, _, hll, hDsmall, _⟩ := hnum K hK T hT
  have hTpos : 0 < T := by
    have hp : 0 < (2 : ℝ)^(((1 / 2 : ℝ) * (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact hp.trans hT
  obtain ⟨hl, hu⟩ := hraw P W hW K n hK64 hKn hH i T hTpos hs
  have hl' : P {ω | ∃ b ∈ j1SourceIdx K (j1SourceRadius Q K),
      ω ∈ j1SmallFullLowerEvent ξ W P K n i T
        (lambdaN ξ W P (n - K)) b} ≤
      ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (Cn * Real.exp (-cn *
          (Real.log (j1CoarseTailParameter ξ 5 T))^2)) +
      ENNReal.ofReal (Cgn * 4^K * Real.exp
        (-(Real.log (j1CoarseTailParameter ξ 5 T))^2 / (2 * σn))) := by
    have hmono := j1_source_union_le_nearby_union P K
      (j1SourceRadius Q K)
      (j1SmallFullLowerEvent ξ W P K n i T (lambdaN ξ W P (n - K)))
    exact hmono.trans (by simpa only [j1SmallFullLowerEvent, Set.mem_ofPred_eq] using hl)
  have hu' : P {ω | ∃ b ∈ j1SourceIdx K (j1SourceRadius Q K),
      ω ∈ j1SmallFullUpperEvent ξ W P hW K n i T
        (lambdaN ξ W P (n - K)) b} ≤
      ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (Cp * Real.exp
          (-cp * (Real.log (j1CoarseTailParameter ξ 5 T))^2 /
            Real.log (Real.log (j1CoarseTailParameter ξ 5 T)))) +
      ENNReal.ofReal (Cgp * 4^K * Real.exp
        (-(Real.log (j1CoarseTailParameter ξ 5 T))^2 / (2 * σp))) := by
    have hmono := j1_source_union_le_nearby_union P K
      (j1SourceRadius Q K)
      (j1SmallFullUpperEvent ξ W P hW K n i T (lambdaN ξ W P (n - K)))
    exact hmono.trans (by simpa only [j1SmallFullUpperEvent, Set.mem_ofPred_eq] using hu)
  exact ⟨hl'.trans (hlowRate K hK2 5 T (by norm_num) hTpos hDsmall),
    hu'.trans (huppRate K hK2 5 T (by norm_num) hTpos hDsmall hs hll)⟩

end SupercriticalLQGUniqueness.B2.DG20Conc

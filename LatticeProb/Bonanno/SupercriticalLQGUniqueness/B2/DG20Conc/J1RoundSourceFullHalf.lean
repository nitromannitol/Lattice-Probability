/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceFullHalf at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfNumeric

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_round_source_full_tails_half
    {ξ p : ℝ} (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ CN cN CP cP : ℝ, ∃ K₀ : ℕ,
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧ 64 ≤ K₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : K₀ ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ)
        (hT : (2 : ℝ)^(((1 / 2 : ℝ) * (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) < T),
        let m := laneBCoarseIndex Q K
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        P {ω | ∃ b ∈ I, ω ∈ j1RoundFullLowerEvent ξ W P K n m T L b} ≤
          ENNReal.ofReal (CN * (5 : ℝ)^K * Real.exp
            (-cN * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1RoundFullUpperEvent ξ W P hW K n m T L b} ≤
          ENNReal.ofReal (CP * (5 : ℝ)^K * Real.exp
            (-cP * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := by
  obtain ⟨R₀, Cn, cn, Cp, cp, Cgn, σn, Cgp, σp,
    hR₀, hCn, hcn, hCp, hcp, hCgn, hσn, hCgp, hσp,
    hraw⟩ := j1_same_p_round_full_raw hunit hp hpHalf C hC
  obtain ⟨cn₀, hcn₀, hlowRate⟩ :=
    j1_source_lower_two_rate ξ Q Cn cn Cgn σn hCn hcn hCgn hσn
  obtain ⟨cp₀, hcp₀, huppRate⟩ :=
    j1_source_upper_two_rate ξ Q Cp cp Cgp σp hCp hcp hCgp hσp
  obtain ⟨K₀, hK₀, hnum⟩ := j1_half_numeric_conditions ξ Q hε R₀
  refine ⟨Cn + Cgn, cn₀, Cp + Cgp, cp₀, K₀,
    by linarith, hcn₀, by linarith, hcp₀, hK₀, ?_⟩
  intro Ω _ P W hW K n hK hKn hH T hT
  dsimp only
  have hK64 : 64 ≤ K := hK₀.trans hK
  have hK2 : 2 ≤ K := by omega
  obtain ⟨_, hmK, hR, hRK, _, hs, hll, _, hDround⟩ := hnum K hK T hT
  have hTpos : 0 < T := by
    have hp : 0 < (2 : ℝ)^(((1 / 2 : ℝ) * (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact hp.trans hT
  obtain ⟨hl, hu⟩ := hraw P W hW K n (laneBCoarseIndex Q K)
    hK64 hKn hmK hR hRK hH T hTpos hs
  have hl' : P {ω | ∃ b ∈ j1SourceIdx K (j1SourceRadius Q K),
      ω ∈ j1RoundFullLowerEvent ξ W P K n (laneBCoarseIndex Q K) T
        (lambdaN ξ W P (n - K)) b} ≤
      ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (Cn * Real.exp (-cn *
          (Real.log (j1CoarseTailParameter ξ
            ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T))^2)) +
      ENNReal.ofReal (Cgn * 4^K * Real.exp
        (-(Real.log (j1CoarseTailParameter ξ
          ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T))^2 / (2 * σn))) := by
    have hmono := j1_source_union_le_nearby_union P K
      (j1SourceRadius Q K)
      (j1RoundFullLowerEvent ξ W P K n (laneBCoarseIndex Q K) T
        (lambdaN ξ W P (n - K)))
    exact hmono.trans (by simpa only [j1RoundFullLowerEvent, Set.mem_ofPred_eq] using hl)
  have hu' : P {ω | ∃ b ∈ j1SourceIdx K (j1SourceRadius Q K),
      ω ∈ j1RoundFullUpperEvent ξ W P hW K n (laneBCoarseIndex Q K) T
        (lambdaN ξ W P (n - K)) b} ≤
      ENNReal.ofReal ((5 : ℝ)^K) *
        ENNReal.ofReal (Cp * Real.exp
          (-cp * (Real.log (j1CoarseTailParameter ξ
            ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T))^2 /
            Real.log (Real.log (j1CoarseTailParameter ξ
              ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T)))) +
      ENNReal.ofReal (Cgp * 4^K * Real.exp
        (-(Real.log (j1CoarseTailParameter ξ
          ((2 : ℝ)^(laneBCoarseIndex Q K + 1)) T))^2 / (2 * σp))) := by
    have hmono := j1_source_union_le_nearby_union P K
      (j1SourceRadius Q K)
      (j1RoundFullUpperEvent ξ W P hW K n (laneBCoarseIndex Q K) T
        (lambdaN ξ W P (n - K)))
    exact hmono.trans (by simpa only [j1RoundFullUpperEvent, Set.mem_ofPred_eq] using hu)
  exact ⟨hl'.trans (hlowRate K hK2 _ T (by positivity) hTpos hDround),
    hu'.trans (huppRate K hK2 _ T (by positivity) hTpos hDround hs hll)⟩

end SupercriticalLQGUniqueness.B2.DG20Conc

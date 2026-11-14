/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceCutoffOfFull at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceCutoffRawOfFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffRate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfLoglog

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_small_source_cutoff_tails_of_full
    {ξ p CN cN CP cP : ℝ} (hξ : 0 < ξ)
    (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (Kfull : ℕ)
    (hCN : 0 < CN) (hcN : 0 < cN) (hCP : 0 < CP) (hcP : 0 < cP)
    (hKfull : 64 ≤ Kfull)
    (hfull : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
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
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) :
    ∃ CN' cN' CP' cP' : ℝ, ∃ K₀ : ℕ,
      0 < CN' ∧ 0 < cN' ∧ 0 < CP' ∧ 0 < cP' ∧ 64 ≤ K₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : K₀ ≤ K) (hKn : K ≤ n)
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
  obtain ⟨Cg, cg, hCg, hcg, hraw⟩ :=
    j1_small_source_cutoff_raw_tails_of_full hξ Q hε C hC Kfull hKfull hfull
  obtain ⟨Kh, hKh⟩ := j1_half_source_loglog_ge_one Q
  obtain ⟨Kf, hKf⟩ := j1_source_loglog_ge_one Q
  let K₀ := max Kfull (max Kh Kf)
  let cN' := j1CutoffRate ξ cN cg
  let cP' := j1CutoffRate ξ cP cg
  refine ⟨CN + Cg, cN', CP + Cg, cP', K₀,
    by linarith, j1_cutoff_rate_pos hξ hcN hcg,
    by linarith, j1_cutoff_rate_pos hξ hcP hcg,
    hKfull.trans (le_max_left _ _), ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT
  dsimp only
  have hKraw : Kfull ≤ K := (le_max_left _ _).trans hK
  have hKhalf : Kh ≤ K := (le_max_left _ _).trans
    ((le_max_right Kfull (max Kh Kf)).trans hK)
  have hKfull : Kf ≤ K := (le_max_right _ _).trans
    ((le_max_right Kfull (max Kh Kf)).trans hK)
  have hK2 : 2 ≤ K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hD : 1 ≤ (K : ℝ)^(3 * Q.ε₀) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ K))
      (by linarith [Q.ε₀_pos])
  have hT1 : 1 < T := by
    have ha : 0 < (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) :=
      Real.rpow_pos_of_pos hKpos _
    exact (Real.one_lt_rpow (by norm_num) ha).trans hT
  have hT' := j1_half_parameter_from_full Q K T hT
  have hll' : 1 ≤ Real.log (Real.log (T^(1 / 2 : ℝ))) :=
    hKh K hKhalf hK2 _ hT'
  have hll : 1 ≤ Real.log (Real.log T) :=
    hKf K hKfull hK2 T hT
  obtain ⟨hl, hu⟩ := hraw P W hW K n hKraw hKn hH i T hT
  have hlowF := j1_cutoff_half_lower_fine_rate ξ cN cg
    ((K : ℝ)^(3 * Q.ε₀)) T hξ hcN hcg
    (by linarith) (by linarith)
  have hlowG := j1_cutoff_gaussian_lower_rate ξ cN cg
    ((K : ℝ)^(3 * Q.ε₀)) T hξ hcN hcg hD
  have huppF := j1_cutoff_half_upper_fine_rate ξ cP cg
    ((K : ℝ)^(3 * Q.ε₀)) T hξ hcP hcg
    (by linarith) hT1 (by linarith)
  have huppG := j1_cutoff_gaussian_upper_rate ξ cP cg
    ((K : ℝ)^(3 * Q.ε₀)) T hξ hcP hcg hD hll
  exact ⟨hl.trans (j1_cutoff_two_rate_absorb K CN Cg _ _ _
    hCN.le hCg.le (Real.exp_pos _).le (Real.exp_pos _).le
    (Real.exp_pos _).le hlowF hlowG),
    hu.trans (j1_cutoff_two_rate_absorb K CP Cg _ _ _
      hCP.le hCg.le (Real.exp_pos _).le (Real.exp_pos _).le
      (Real.exp_pos _).le huppF huppG)⟩

end SupercriticalLQGUniqueness.B2.DG20Conc

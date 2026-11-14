/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPSourceClosure at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallFullUpperRaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfNumeric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceCutoffOfFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfStartMono
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPCutoffFine
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceFineSameP
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceFull
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceCutoff
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffRate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_source_fine_full_cutoff_fixed_p
    {ξ : ℝ} (hξ : 0 < ξ) (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
     :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ (C : ℝ) (hC : 0 ≤ C),
        ∃ C₀ c₀ : ℝ, ∃ K₀ : ℕ, ∃ Cf cf : ℝ, ∃ Kfine : ℕ,
      0 < C₀ ∧ 0 < c₀ ∧ 64 ≤ K₀ ∧
      0 < Cf ∧ 0 < cf ∧ 64 ≤ Kfine ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : Kfine ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ) (hT : (2 : ℝ)^(Real.sqrt K) < T),
        let m := laneBCoarseIndex Q K
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        (∀ i : Bool,
          P {ω | ∃ b ∈ I, ω ∈ j1SmallFineLowerEvent ξ W P K n i T L b} ≤
            ENNReal.ofReal (Cf * (5 : ℝ)^K *
              Real.exp (-cf * (Real.log T)^2)) ∧
          P {ω | ∃ b ∈ I,
            ω ∈ j1SmallFineUpperEvent ξ W P hW K n hKn i T L b} ≤
            ENNReal.ofReal (Cf * (5 : ℝ)^K * Real.exp
              (-cf * (Real.log T)^2 / Real.log (Real.log T)))) ∧
        P {ω | ∃ b ∈ I, ω ∈ j1RoundFineLowerEvent ξ W P K n m T L b} ≤
          ENNReal.ofReal (Cf * (5 : ℝ)^K *
            Real.exp (-cf * (Real.log T)^2)) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1RoundFineUpperEvent ξ W P hW K n m hKn T L b} ≤
          ENNReal.ofReal (Cf * (5 : ℝ)^K * Real.exp
            (-cf * (Real.log T)^2 / Real.log (Real.log T)))) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : K₀ ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ)
        (hT : (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T),
        let m := laneBCoarseIndex Q K
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        ((∀ i : Bool,
          P {ω | ∃ b ∈ I, ω ∈ j1SmallFullLowerEvent ξ W P K n i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
              (-c₀ * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
          P {ω | ∃ b ∈ I,
            ω ∈ j1SmallFullUpperEvent ξ W P hW K n i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
              (-c₀ * (Real.log T)^2 /
                ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) ∧
        P {ω | ∃ b ∈ I, ω ∈ j1RoundFullLowerEvent ξ W P K n m T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
            (-c₀ * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1RoundFullUpperEvent ξ W P hW K n m T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
            (-c₀ * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) ∧
        ((∀ i : Bool,
          P {ω | ∃ b ∈ I, ω ∈ j1SmallCutLowerEvent ξ Q W P K n i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
              (-c₀ * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
          P {ω | ∃ b ∈ I,
            ω ∈ j1SmallCutUpperEvent ξ Q W P hW K n i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
              (-c₀ * (Real.log T)^2 /
                ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) ∧
        P {ω | ∃ b ∈ I, ω ∈ j1RoundCutLowerEvent ξ Q W P K n m T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
            (-c₀ * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1RoundCutUpperEvent ξ Q W P hW K n m T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
            (-c₀ * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) := by
  obtain ⟨p, hp, hpHalf, hunit, hfixed⟩ :=
    j1_fixed_p_small_full_half_and_cutoff_with_fine hξ Q hε
  refine ⟨p, hp, hpHalf, hunit, ?_⟩
  intro C hC
  obtain ⟨CNf, cNf, CPf, cPf, CNs, cNs, CPs, cPs, Ks,
    hCNf, hcNf, hCPf, hcPf,
    hCNs, hcNs, hCPs, hcPs, hKs, hfineSmall, hfullS,
    CNcs, cNcs, CPcs, cPcs, Kcs,
    hCNcs, hcNcs, hCPcs, hcPcs, hKcs, hcutS⟩ := hfixed C hC
  obtain ⟨CNr, cNr, CPr, cPr, Kr,
    hCNr, hcNr, hCPr, hcPr, hKr, hfullR⟩ :=
    j1_round_source_full_tails hunit hp hpHalf Q hε C hC
  obtain ⟨CNcr, cNcr, CPcr, cPcr, Kcr,
    hCNcr, hcNcr, hCPcr, hcPcr, hKcr, hcutR⟩ :=
    j1_round_source_cutoff_tails hξ hunit hp hpHalf Q hε C hC
  obtain ⟨Cf, cf, Kfine, hCf, hcf, hKfine, hfineSource⟩ :=
    j1_source_fine_four_tails_of_same_p hξ Q hε C hC
      hp hpHalf hCNf hcNf hCPf hcPf hunit hfineSmall
  obtain ⟨Klog, hKlog⟩ := j1_source_loglog_ge_one Q
  let K₀ := max Ks (max Kcs (max Kr (max Kcr Klog)))
  let C₀ := CNs + CPs + CNcs + CPcs + CNr + CPr + CNcr + CPcr
  let c₀ := min (min (min cNs cPs) (min cNcs cPcs))
    (min (min cNr cPr) (min cNcr cPcr))
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact lt_min (lt_min (lt_min hcNs hcPs) (lt_min hcNcs hcPcs))
      (lt_min (lt_min hcNr hcPr) (lt_min hcNcr hcPcr))
  refine ⟨C₀, c₀, K₀, Cf, cf, Kfine,
    hC₀, hc₀, hKs.trans (le_max_left _ _),
    hCf, hcf, hKfine, hfineSource, ?_⟩
  intro Ω _ P W hW K n hK hKn hH T hT
  dsimp only
  have hKsK : Ks ≤ K := (le_max_left _ _).trans hK
  have hKcsK : Kcs ≤ K := (le_max_left _ _).trans
    ((le_max_right Ks _).trans hK)
  have hKrK : Kr ≤ K := (le_max_left _ _).trans
    ((le_max_right Kcs _).trans ((le_max_right Ks _).trans hK))
  have hKcrK : Kcr ≤ K := (le_max_left _ _).trans
    ((le_max_right Kr _).trans ((le_max_right Kcs _).trans
      ((le_max_right Ks _).trans hK)))
  have hKlogK : Klog ≤ K := (le_max_right _ _).trans
    ((le_max_right Kr _).trans ((le_max_right Kcs _).trans
      ((le_max_right Ks _).trans hK)))
  have hK2 : 2 ≤ K := by omega
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hD : 0 < (K : ℝ)^(3 * Q.ε₀) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hll : 1 ≤ Real.log (Real.log T) := hKlog K hKlogK hK2 T hT
  have hDu : 0 < (K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T) :=
    mul_pos hD (by linarith)
  have hCNsC : CNs ≤ C₀ := by dsimp [C₀]; linarith
  have hCPsC : CPs ≤ C₀ := by dsimp [C₀]; linarith
  have hCNcsC : CNcs ≤ C₀ := by dsimp [C₀]; linarith
  have hCPcsC : CPcs ≤ C₀ := by dsimp [C₀]; linarith
  have hCNrC : CNr ≤ C₀ := by dsimp [C₀]; linarith
  have hCPrC : CPr ≤ C₀ := by dsimp [C₀]; linarith
  have hCNcrC : CNcr ≤ C₀ := by dsimp [C₀]; linarith
  have hCPcrC : CPcr ≤ C₀ := by dsimp [C₀]; linarith
  have hcNsC : c₀ ≤ cNs := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hcPsC : c₀ ≤ cPs := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hcNcsC : c₀ ≤ cNcs := ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcPcsC : c₀ ≤ cPcs := ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hcNrC : c₀ ≤ cNr := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hcPrC : c₀ ≤ cPr := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hcNcrC : c₀ ≤ cNcr := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcPcrC : c₀ ≤ cPcr := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsF i := hfullS P W hW K n hKsK hKn hH i T
    (j1_half_start_of_full Q K T hT)
  have hsC i := hcutS P W hW K n hKcsK hKn hH i T hT
  obtain ⟨hrFl, hrFu⟩ := hfullR P W hW K n hKrK hKn hH T hT
  obtain ⟨hrCl, hrCu⟩ := hcutR P W hW K n hKcrK hKn hH T hT
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ⟨(hsF i).1.trans
        (j1_source_rate_weaken K _ T CNs cNs C₀ c₀ hD
          hCNs.le hCNsC hcNsC),
        (hsF i).2.trans
        (j1_source_rate_weaken K _ T CPs cPs C₀ c₀ hDu
          hCPs.le hCPsC hcPsC)⟩
    · exact hrFl.trans
        (j1_source_rate_weaken K _ T CNr cNr C₀ c₀ hD
          hCNr.le hCNrC hcNrC)
    · exact hrFu.trans
        (j1_source_rate_weaken K _ T CPr cPr C₀ c₀ hDu
          hCPr.le hCPrC hcPrC)
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ⟨(hsC i).1.trans
        (j1_source_rate_weaken K _ T CNcs cNcs C₀ c₀ hD
          hCNcs.le hCNcsC hcNcsC),
        (hsC i).2.trans
        (j1_source_rate_weaken K _ T CPcs cPcs C₀ c₀ hDu
          hCPcs.le hCPcsC hcPcsC)⟩
    · exact hrCl.trans
        (j1_source_rate_weaken K _ T CNcr cNcr C₀ c₀ hD
          hCNcr.le hCNcrC hcNcrC)
    · exact hrCu.trans
        (j1_source_rate_weaken K _ T CPcr cPcr C₀ c₀ hDu
          hCPcr.le hCPcrC hcPcrC)

end SupercriticalLQGUniqueness.B2.DG20Conc

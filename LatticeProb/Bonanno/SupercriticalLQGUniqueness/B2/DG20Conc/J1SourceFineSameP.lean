/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceFineSameP at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FineEvents
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffRate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_source_fine_four_tails_of_same_p
    {ξ p CNs cNs CPs cPs : ℝ} (hξ : 0 < ξ)
    (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hp : 0 < p) (hpHalf : p < 2⁻¹)
    (hCNs : 0 < CNs) (hcNs : 0 < cNs)
    (hCPs : 0 < CPs) (hcPs : 0 < cPs)
    (hunit : LaneA2HasUnitTails.{u} ξ p)
    (hsmall : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
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
            ENNReal.ofReal (CNs * Real.exp (-cNs * (Real.log T)^2)) ∧
        P {ω | ∃ b ∈ T20B.nearIdx K,
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
            (lfppContMetric ξ (fun z => phiMN W P K n z ω)
              ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
              (laneBBlockAround i (T20.dyCenter K b) K)
              (j1BlockInner i (T20.dyCenter K b) K)
              (j1BlockOuter i (T20.dyCenter K b) K)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CPs * Real.exp
              (-cPs * (Real.log T)^2 / Real.log (Real.log T)))) :
    ∃ C₀ c₀ : ℝ, ∃ K₀ : ℕ,
      0 < C₀ ∧ 0 < c₀ ∧ 64 ≤ K₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : K₀ ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ) (hT : (2 : ℝ)^(Real.sqrt K) < T),
        let m := laneBCoarseIndex Q K
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        (∀ i : Bool,
          P {ω | ∃ b ∈ I, ω ∈ j1SmallFineLowerEvent ξ W P K n i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K *
              Real.exp (-c₀ * (Real.log T)^2)) ∧
          P {ω | ∃ b ∈ I,
            ω ∈ j1SmallFineUpperEvent ξ W P hW K n hKn i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
              (-c₀ * (Real.log T)^2 / Real.log (Real.log T)))) ∧
        P {ω | ∃ b ∈ I, ω ∈ j1RoundFineLowerEvent ξ W P K n m T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K *
            Real.exp (-c₀ * (Real.log T)^2)) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1RoundFineUpperEvent ξ W P hW K n m hKn T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
            (-c₀ * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨R₀, CNr, cNr, CPr, cPr,
    hR₀, hCNr, hcNr, hCPr, hcPr, hround⟩ :=
    j1_same_p_physical_round_all hunit hp hpHalf C hC
  obtain ⟨Krange, hrange⟩ := j1_round_scale_range Q R₀ hε
  let K₀ := max 64 Krange
  let C₀ := CNs + CPs + CNr + CPr
  let c₀ := min (min cNs cPs) (min cNr cPr)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact lt_min (lt_min hcNs hcPs) (lt_min hcNr hcPr)
  refine ⟨C₀, c₀, K₀, hC₀, hc₀, le_max_left _ _, ?_⟩
  intro Ω _ P W hW K n hK hKn hH T hT
  dsimp only
  have hK64 : 64 ≤ K := (le_max_left _ _).trans hK
  have hKr : Krange ≤ K := (le_max_right _ _).trans hK
  have hT3 : 3 < T := j1_fine_start_gt_three hK64 hT
  have hll : 0 < Real.log (Real.log T) := j1_fine_loglog_pos hT3
  obtain ⟨hmK, hR, hRK⟩ := hrange K hKr hK64
  have hR' : R₀ ≤ (2 : ℝ)^(laneBCoarseIndex Q K) := hR
  have hsmall' i := hsmall P W hW K n hK64 hKn hH i T hT3
  obtain ⟨hrl, hru⟩ := hround P W hW K n (laneBCoarseIndex Q K)
    hK64 hKn (by omega) hR' hRK hH T hT3
  have hCNsC : CNs ≤ C₀ := by dsimp [C₀]; linarith
  have hCPsC : CPs ≤ C₀ := by dsimp [C₀]; linarith
  have hCNrC : CNr ≤ C₀ := by dsimp [C₀]; linarith
  have hCPrC : CPr ≤ C₀ := by dsimp [C₀]; linarith
  have hcNsC : c₀ ≤ cNs := (min_le_left _ _).trans (min_le_left _ _)
  have hcPsC : c₀ ≤ cPs := (min_le_left _ _).trans (min_le_right _ _)
  have hcNrC : c₀ ≤ cNr := (min_le_right _ _).trans (min_le_left _ _)
  have hcPrC : c₀ ≤ cPr := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hs := (j1_source_union_le_near_union P K
      (j1SourceRadius Q K)
      (j1SmallFineLowerEvent ξ W P K n i T
        (lambdaN ξ W P (n - K)))).trans
      (by simpa only [j1SmallFineLowerEvent, Set.mem_ofPred_eq]
        using (hsmall' i).1)
    have hu := (j1_source_union_le_near_union P K
      (j1SourceRadius Q K)
      (j1SmallFineUpperEvent ξ W P hW K n hKn i T
        (lambdaN ξ W P (n - K)))).trans
      (by simpa only [j1SmallFineUpperEvent, Set.mem_ofPred_eq]
        using (hsmall' i).2)
    exact ⟨(hs.trans_eq (j1_fine_prob_scale_eq K CNs
      (Real.exp (-cNs * (Real.log T)^2)))).trans
        (by simpa only [div_one] using
          (j1_source_rate_weaken K 1 T CNs cNs C₀ c₀
            (by norm_num) hCNs.le hCNsC hcNsC)),
      (hu.trans_eq (j1_fine_prob_scale_eq K CPs
        (Real.exp (-cPs * (Real.log T)^2 / Real.log (Real.log T))))).trans
        (j1_source_rate_weaken K (Real.log (Real.log T)) T
          CPs cPs C₀ c₀ hll hCPs.le hCPsC hcPsC)⟩
  · have hr := (j1_source_union_le_near_union P K
      (j1SourceRadius Q K)
      (j1RoundFineLowerEvent ξ W P K n (laneBCoarseIndex Q K) T
        (lambdaN ξ W P (n - K)))).trans
      (by simpa only [j1RoundFineLowerEvent, Set.mem_ofPred_eq]
        using hrl)
    exact (hr.trans_eq (j1_fine_prob_scale_eq K CNr
      (Real.exp (-cNr * (Real.log T)^2)))).trans
        (by simpa only [div_one] using
          (j1_source_rate_weaken K 1 T CNr cNr C₀ c₀
            (by norm_num) hCNr.le hCNrC hcNrC))
  · have hr := (j1_source_union_le_near_union P K
      (j1SourceRadius Q K)
      (j1RoundFineUpperEvent ξ W P hW K n (laneBCoarseIndex Q K)
        hKn T (lambdaN ξ W P (n - K)))).trans
      (by simpa only [j1RoundFineUpperEvent, Set.mem_ofPred_eq]
        using hru)
    exact (hr.trans_eq (j1_fine_prob_scale_eq K CPr
      (Real.exp (-cPr * (Real.log T)^2 / Real.log (Real.log T))))).trans
        (j1_source_rate_weaken K (Real.log (Real.log T)) T
          CPr cPr C₀ c₀ hll hCPr.le hCPrC hcPrC)

end SupercriticalLQGUniqueness.B2.DG20Conc

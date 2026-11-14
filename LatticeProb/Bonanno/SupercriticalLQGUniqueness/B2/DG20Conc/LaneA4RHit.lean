/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RHit at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDefs
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DDen
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P21Ratio
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CDefs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.LiminfLimsup
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1QuantileStep
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Step2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6TailsAB2
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BRect
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Zero
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneALaw
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneATails
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Eq698Main
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2QuantileBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.Median.Bridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitTails
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteExitMeet
import LatticeProb.Bonanno.LQGMetric.LFPP.Length
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DGeom
import Mathlib.Data.Fintype.EquivFin
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LoopSep
import Mathlib.Analysis.Complex.Convex
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LogCross
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps
import LatticeProb.Bonanno.LQGMetric.LFPP.PathConcat
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.RSWPath
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20CCross
import LatticeProb.Bonanno.LQGMetric.LFPP.PathAnalytic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DiamGeo
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Blocks
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBObigGaussian
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Scale
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Law
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20BBlocks
import Mathlib.Data.Int.Interval
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenHeat
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Families
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.LFPP.WeylUpper
import LatticeProb.Bonanno.LQGMetric.Metric.WeylPathLength
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20DNum
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBProbabilityTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearbyIdx
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBScaleCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRadius
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRoundCutoffTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RPay

 













set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

attribute [local instance] Classical.propDecidable

theorem laneSourceIdx_subset_nearIdx (Q : PsiParams) (K : ℕ) :
    laneSourceIdx Q K ⊆ T20B.nearIdx K := by
  intro b hb
  classical
  unfold laneSourceIdx j1SourceIdx at hb
  exact j1_nearbyIdx_mem_nearIdx (Finset.mem_filter.mp hb).1

theorem laneC1R_four_source_radius_lt_one (Q : PsiParams) (hε : Q.ε₀ ≤ 1) {K : ℕ}
    (hK : 8 ≤ K) : 4 * LaneCInputs.sourceRadius K (laneBCoarseIndex Q K) < 1 ∧
      laneBCoarseIndex Q K ≤ K := by
  have hK2 : 2 ≤ K := by omega
  have hmK := laneB_coarseIndex_add_one_le Q K hε hK2
  have h8 := laneC_source_outer_radius_lt_eighth hK hmK hε
    (laneB_coarseIndex_radius Q K hK2).1
  exact ⟨by linarith, by omega⟩

 
theorem laneA3_across_sum_le.{u} :
  ∀ (Q : PsiParams), Q.ε₀ ≤ 1 → ∀ (ξ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (n K : ℕ), 8 ≤ K →
    ∀ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j)) →
    ∀ ω : Ω,
      ∑ b ∈ T20B.nearIdx K,
          (laneCEventualHit γ n K (laneBCoarseIndex Q K) b).indicator
            (laneA3Across P W Q ξ n K b) ω ≤
        (((4 * 2 ^ laneBCoarseIndex Q K + 1) ^ 2 : ℕ) : ℝ≥0∞) *
          rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
  intro Q hε ξ Ω _ P W n K hK γ hγ ω
  obtain ⟨hr4, hmK⟩ := laneC1R_four_source_radius_lt_one Q hε hK
  exact laneA3R_eventual_hit_mass P W Q ξ n K _ hr4 γ hγ (T20B.nearIdx K) _
    (fun q => laneA3R_overlap_card hmK _ q) ω

 
theorem laneA4_eventualHit_across_le.{u} :
  ∀ (Q : PsiParams), Q.ε₀ ≤ 1 → ∀ (ξ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (n K : ℕ), 8 ≤ K →
    ∀ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j)) →
    ∀ b ∈ T20B.nearIdx K,
      ∀ ω ∈ laneCEventualHit γ n K (laneBCoarseIndex Q K) b,
        laneA3Across P W Q ξ n K b ω ≤
          rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
  intro Q hε ξ Ω _ P W n K hK γ hγ b _ ω hω
  obtain ⟨hr4, -⟩ := laneC1R_four_source_radius_lt_one Q hε hK
  have h := laneA3R_eventual_hit_mass P W Q ξ n K _ hr4 γ hγ {b} 1
    (fun q => (Finset.card_filter_le _ _).trans (by simp)) ω
  rw [Finset.sum_singleton, Set.indicator_of_mem hω, Nat.cast_one, one_mul] at h
  exact h

 

def laneA4Regular {Ω : Type*} [MeasurableSpace Ω] (Q : PsiParams)
    (ξ Qe ζ : ℝ) (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (n K : ℕ) : Set Ω :=
  {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω ≤
        (2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)) *
          (2 : ℝ) ^ (-(1 - ξ * Qe - ζ) * (K : ℝ)) * lambdaN ξ W P (n - K) ∧
      ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)))⁻¹ *
          (2 : ℝ) ^ (-(1 - ξ * Qe + ζ) * (K : ℝ)) * lambdaN ξ W P (n - K) ≤
        lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω ∧
      ∀ b ∈ laneSourceIdx Q K,
        ω ∉ j1RoundCutLowerEvent ξ Q W P K n (laneBCoarseIndex Q K)
          ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ))) (lambdaN ξ W P (n - K)) b ∧
        ω ∉ j1RoundCutUpperEvent ξ Q W P hW K n (laneBCoarseIndex Q K)
          ((2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ))) (lambdaN ξ W P (n - K)) b}

 

theorem laneA4_hit_truncation_source.{u} :
  ∀ (Q : PsiParams), Q.ε₀ ≤ 1 → ∀ (ξ Qe ζ : ℝ), 0 < ξ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ), 8 ≤ K → K ≤ n →
    ∀ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel ξ Q W P (((j : ℝ) + 1)⁻¹) (γ j)) →
    ∀ b ∈ laneSourceIdx Q K,
      laneCEventualHit γ n K (laneBCoarseIndex Q K) b ∩
          laneA4Regular Q ξ Qe ζ P W hW n K ⊆
        {ω | phiMN W P 0 K (T20.dyCenter K b) ω ≤
          (Qe + (ζ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ) *
            ((K : ℝ) * Real.log 2)} := by
  intro Q hε ξ Qe ζ hξ Ω _ P W hW n K hK hKn γ hγ b hb ω ⟨hF, h1, h2, h34⟩
  have hbn := laneSourceIdx_subset_nearIdx Q K hb
  have hacross := laneA4_eventualHit_across_le Q hε ξ P W n K hK γ hγ b hbn ω hF
  have hlow := (h34 b hb).1
  set φ := phiMN W P 0 K (T20.dyCenter K b) ω
  set lam := lambdaN ξ W P (n - K)
  have hlam : 0 < lam := lambdaN_pos hW (n - K)
  set Lr := lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hLfin : rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) (hψ.cont ω)
  have hLr : rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) = ENNReal.ofReal Lr :=
    (ENNReal.ofReal_toReal hLfin).symm
  set a := Real.log 2
  have ha : 0 < a := Real.log_pos (by norm_num)
  set κ := (K : ℝ) ^ (2 / 3 : ℝ)
  have hτ : (2 : ℝ) ^ κ = Real.exp (κ * a) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hup : (2 : ℝ) ^ (-(1 - ξ * Qe - ζ) * (K : ℝ)) = Real.exp (-(1 - ξ * Qe - ζ) * K * a) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [show Real.log 2 = a from rfl]
    ring
  have hK2 : (2 : ℝ)⁻¹ ^ K = Real.exp (-(K * a)) := by
    have hl : Real.log ((2 : ℝ)⁻¹ ^ K) = -(K * a) := by
      rw [Real.log_pow, Real.log_inv]; ring
    rw [← hl, Real.exp_log (by positivity)]
  
  have hlowr : ((2 : ℝ) ^ κ)⁻¹ * ((2 : ℝ)⁻¹ ^ K * lam) ≤ Real.exp (-ξ * φ) * Lr := by
    have hnot : ¬ (ENNReal.ofReal (Real.exp (-ξ * φ)) *
        laneA3Across P W Q ξ n K b ω < ENNReal.ofReal (((2 : ℝ) ^ κ)⁻¹ *
          ((2 : ℝ)⁻¹ ^ K * lam))) := hlow
    push Not at hnot
    have h3 : ENNReal.ofReal (((2 : ℝ) ^ κ)⁻¹ * ((2 : ℝ)⁻¹ ^ K * lam)) ≤
        ENNReal.ofReal (Real.exp (-ξ * φ) * Lr) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← hLr]
      exact hnot.trans (mul_le_mul' le_rfl hacross)
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le
      ENNReal.toReal_nonneg)).mp h3
  
  have hcomb : ((2 : ℝ) ^ κ)⁻¹ * ((2 : ℝ)⁻¹ ^ K * lam) ≤
      Real.exp (-ξ * φ) * ((2 : ℝ) ^ κ * (2 : ℝ) ^ (-(1 - ξ * Qe - ζ) * (K : ℝ)) * lam) :=
    hlowr.trans (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le)
  rw [hτ, hup, hK2] at hcomb
  have hexp : Real.exp (-(κ * a) - K * a) ≤
      Real.exp (-ξ * φ + κ * a + (-(1 - ξ * Qe - ζ) * K * a)) := by
    have e1 : (Real.exp (κ * a))⁻¹ * (Real.exp (-(K * a)) * lam) =
        Real.exp (-(κ * a) - K * a) * lam := by
      rw [← Real.exp_neg, sub_eq_add_neg, Real.exp_add]; ring
    have e2 : Real.exp (-ξ * φ) * (Real.exp (κ * a) *
        Real.exp (-(1 - ξ * Qe - ζ) * K * a) * lam) =
        Real.exp (-ξ * φ + κ * a + (-(1 - ξ * Qe - ζ) * K * a)) * lam := by
      rw [Real.exp_add, Real.exp_add]; ring
    rw [e1, e2] at hcomb
    exact le_of_mul_le_mul_right hcomb hlam
  have hlin := Real.exp_le_exp.mp hexp
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hκ : κ = (K : ℝ) ^ (-(1 / 3 : ℝ)) * K := by
    have : (K : ℝ) ^ (-(1 / 3 : ℝ)) * K = (K : ℝ) ^ (-(1 / 3 : ℝ) + 1) := by
      rw [Real.rpow_add hKpos, Real.rpow_one]
    rw [this]
    norm_num [κ]
  show φ ≤ (Qe + (ζ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ) * ((K : ℝ) * a)
  have hξφ : ξ * φ ≤ 2 * κ * a + (ξ * Qe + ζ) * K * a := by nlinarith
  rw [hκ] at hξφ
  have : (Qe + (ζ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ) * ((K : ℝ) * a) =
      (ξ * Qe * K * a + ζ * K * a + 2 * ((K : ℝ) ^ (-(1 / 3 : ℝ)) * K) * a) / ξ := by
    field_simp
    ring
  rw [this, le_div_iff₀ hξ]
  nlinarith

end SupercriticalLQGUniqueness.B2.DG20Conc

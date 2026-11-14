/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RDefs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
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
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom
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
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCInputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBScaleCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRadius
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1OscExtended
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigRealUniform
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceIdx
import Mathlib.Analysis.Complex.ExponentialBounds
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneC1RDefs
import Mathlib.Probability.Kernel.Condexp
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1FixedPSourceClosure

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

 

def J1FixedPAt.{v} (Q : PsiParams) (ξ p : ℝ) : Prop :=
      ∀ (C : ℝ) (hC : 0 ≤ C),
        ∃ C₀ c₀ : ℝ, ∃ K₀ : ℕ, ∃ Cf cf : ℝ, ∃ Kfine : ℕ,
      0 < C₀ ∧ 0 < c₀ ∧ 64 ≤ K₀ ∧
      0 < Cf ∧ 0 < cf ∧ 64 ≤ Kfine ∧
      (∀ {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω)
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
      ∀ {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω)
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
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))))

theorem j1_fixed_p_at.{v} {ξ : ℝ} (hξ : 0 < ξ) (Q : PsiParams) (hε : Q.ε₀ ≤ 1) :
    ∃ p : ℝ, 0 < p ∧ p < 2⁻¹ ∧ LaneA2HasUnitTails.{v} ξ p ∧ J1FixedPAt.{v} Q ξ p :=
  j1_source_fine_full_cutoff_fixed_p.{v} hξ Q hε
theorem j1FixedPAt_roundCut.{v} (Q : PsiParams) (ξ p : ℝ) :
  J1FixedPAt.{v} Q ξ p →
  ∀ (C : ℝ), 0 ≤ C → ∃ C₀ c₀ : ℝ, ∃ K₀ : ℕ, 0 < C₀ ∧ 0 < c₀ ∧
    ∀ {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (K n : ℕ),
      K₀ ≤ K → K ≤ n →
      LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
        Real.exp (C * Real.sqrt (K : ℝ)) →
      ∀ T : ℝ, (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Q.ε₀)) < T →
      P {ω | ∃ b ∈ laneSourceIdx Q K, ω ∈ j1RoundCutLowerEvent ξ Q W P K n
          (laneBCoarseIndex Q K) T (lambdaN ξ W P (n - K)) b} ≤
        ENNReal.ofReal (C₀ * (5 : ℝ) ^ K * Real.exp
          (-c₀ * (Real.log T) ^ 2 / (K : ℝ) ^ (3 * Q.ε₀))) ∧
      P {ω | ∃ b ∈ laneSourceIdx Q K, ω ∈ j1RoundCutUpperEvent ξ Q W P hW K n
          (laneBCoarseIndex Q K) T (lambdaN ξ W P (n - K)) b} ≤
        ENNReal.ofReal (C₀ * (5 : ℝ) ^ K * Real.exp
          (-c₀ * (Real.log T) ^ 2 /
            ((K : ℝ) ^ (3 * Q.ε₀) * Real.log (Real.log T)))) := by
  intro hJ C hC
  obtain ⟨C₀, c₀, K₀, Cf, cf, Kfine, hC₀, hc₀, -, -, -, -, -, hfull⟩ := hJ C hC
  refine ⟨C₀, c₀, K₀, hC₀, hc₀, ?_⟩
  intro Ω _ P W hW K n hK hKn hH T hT
  have h := hfull P W hW K n hK hKn hH T hT
  dsimp only at h
  exact ⟨h.2.2.1, h.2.2.2⟩

 
@[instance_reducible] def laneFineStar {Ω : Type*} [MeasurableSpace Ω]
    (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (K n : ℕ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω z => psiMN Q W P K n z ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ)) ⊔
    ⨆ b ∈ T20B.nearIdx K, MeasurableSpace.comap
      (fun ω z => T20B.blkKn Q W P K n b z ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ))

 
def laneA3HitWeight {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K : ℕ) (b : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  (laneCEventualHit γ n K (laneBCoarseIndex Q K) b).indicator
    (fun x => laneA3Around P W hW Q ξ n K b x /
      rectLen ξ (fun z => psiMN Q W P 0 n z x) (rectAB 1 1)) ω

end SupercriticalLQGUniqueness.B2.DG20Conc

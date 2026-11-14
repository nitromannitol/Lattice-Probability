/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundFullLowerRaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearRoundFullTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearRoundOsc
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseScaledThreshold
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RealProb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_round_full_lower_raw_of_fine_tail (ξ : ℝ) :
    ∃ C σ : ℝ, 0 < C ∧ 0 < σ ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (K n m : ℕ) (hKn : K ≤ n) (hmK : m + 1 ≤ K)
      (T L : ℝ) (hT : 0 < T)
      (hs : 3 < j1CoarseTailParameter ξ ((2 : ℝ) ^ (m + 1)) T)
      (A : ℝ≥0∞),
      (P {ω | ∃ b ∈ T20B.nearIdx K,
        crossLenIn ξ (fun z => phiMN W P K n z ω)
          (j1SourceCross K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b) <
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal
              ((j1CoarseTailParameter ξ ((2 : ℝ) ^ (m + 1)) T)⁻¹ * L)} ≤ A) →
      P {ω | ∃ b ∈ j1NearbyIdx K,
        ENNReal.ofReal
          (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
          crossLenIn ξ (fun z => phiMN W P 0 n z ω)
            (j1SourceCross K m b)
            (LaneCInputs.sourceInner K m b)
            (LaneCInputs.sourceOuter K m b) <
          ENNReal.ofReal
            (T⁻¹ * ((2 : ℝ)⁻¹ ^ K * L))} ≤
        A + ENNReal.ofReal
          (C * 4 ^ K * Real.exp (-(Real.log
            (j1CoarseTailParameter ξ ((2 : ℝ) ^ (m + 1)) T))^2 /
              (2 * σ))) := by
  obtain ⟨C, σ, hC, hσ, hosc⟩ :=
    j1_nearby_round_oscillation_bad_event
  refine ⟨C, σ, hC, hσ, ?_⟩
  intro Ω _ P W hW K n m hKn hmK T L hT hs A hFine
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let B : ℝ := (2 : ℝ) ^ (m + 1)
  let s := j1CoarseTailParameter ξ B T
  let r : ℝ := (2 : ℝ)⁻¹ ^ K
  let Bad : Set Ω := {ω | ∃ b ∈ j1NearbyIdx K,
    ∃ z ∈ j1SourceCross K m b,
      B * Real.log s < |phiMN W P 0 K z ω -
        phiMN W P 0 K (T20.dyCenter K b) ω|}
  have hBad : P Bad ≤ ENNReal.ofReal
      (C * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σ))) := by
    have hreal := hosc P W hW K m hmK (Real.log s)
      (Real.log_pos (by linarith [hs])).le
    exact j1_prob_le_of_real_le P Bad hreal
  let E : ℤ × ℤ → Set Ω := fun b =>
    {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (j1SourceCross K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b) <
      ENNReal.ofReal r * ENNReal.ofReal (s⁻¹ * L)}
  have hFineNear : P {ω | ∃ b ∈ j1NearbyIdx K, ω ∈ E b} ≤ A :=
    (j1_nearby_union_le_near_union P K E).trans hFine
  have hth :
      ENNReal.ofReal (Real.exp (|ξ| * (B * Real.log s))) *
        ENNReal.ofReal (T⁻¹ * (r * L)) =
      ENNReal.ofReal r * ENNReal.ofReal (s⁻¹ * L) := by
    have he : |ξ| * (B * Real.log s) =
        |ξ| * B * Real.log s := by ring
    rw [he]
    exact j1_coarse_scaled_lower_threshold ξ B T r L
      (by dsimp [B]; positivity) hT (by dsimp [r]; positivity)
  have htr := (j1_nearby_round_full_field_transfer (m := m)
    P W hW ξ hKn (B * Real.log s)
    (ENNReal.ofReal (T⁻¹ * (r * L)))
    (ENNReal.ofReal (s * (r * L)))).1
  rw [hth] at htr
  calc
    P {ω | ∃ b ∈ j1NearbyIdx K,
      ENNReal.ofReal
        (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        crossLenIn ξ (fun z => phiMN W P 0 n z ω)
          (j1SourceCross K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b) <
        ENNReal.ofReal (T⁻¹ * (r * L))} ≤
      P {ω | ∃ b ∈ j1NearbyIdx K, ω ∈ E b} + P Bad := htr
    _ ≤ A + ENNReal.ofReal
        (C * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σ))) :=
      add_le_add hFineNear hBad

end SupercriticalLQGUniqueness.B2.DG20Conc

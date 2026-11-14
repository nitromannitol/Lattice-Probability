/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallFullLowerRaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearSmallFullTransfer
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearSmallOsc
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseScaledThreshold
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RealProb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_small_full_lower_raw_of_fine_tail (ξ : ℝ) :
    ∃ C σ : ℝ, 0 < C ∧ 0 < σ ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (K n : ℕ) (hK : 3 ≤ K) (hKn : K ≤ n)
      (i : Bool) (T L : ℝ) (hT : 0 < T)
      (hs : 3 < j1CoarseTailParameter ξ 5 T)
      (A : ℝ≥0∞),
      (P {ω | ∃ b ∈ T20B.nearIdx K,
        crossLenIn ξ (fun z => phiMN W P K n z ω)
          (laneBBlockAnnulus i (T20.dyCenter K b) K)
          (j1BlockInner i (T20.dyCenter K b) K)
          (j1BlockOuter i (T20.dyCenter K b) K) <
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal
              ((j1CoarseTailParameter ξ 5 T)⁻¹ * L)} ≤ A) →
      P {ω | ∃ b ∈ j1NearbyIdx K,
        ENNReal.ofReal
          (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
          crossLenIn ξ (fun z => phiMN W P 0 n z ω)
            (laneBBlockAnnulus i (T20.dyCenter K b) K)
            (j1BlockInner i (T20.dyCenter K b) K)
            (j1BlockOuter i (T20.dyCenter K b) K) <
          ENNReal.ofReal
            (T⁻¹ * ((2 : ℝ)⁻¹ ^ K * L))} ≤
        A + ENNReal.ofReal
          (C * 4 ^ K * Real.exp (-(Real.log
            (j1CoarseTailParameter ξ 5 T))^2 / (2 * σ))) := by
  obtain ⟨C, σ, hC, hσ, hosc⟩ :=
    j1_nearby_small_oscillation_bad_event
  refine ⟨C, σ, hC, hσ, ?_⟩
  intro Ω _ P W hW K n hK hKn i T L hT hs A hFine
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let s := j1CoarseTailParameter ξ 5 T
  let r : ℝ := (2 : ℝ)⁻¹ ^ K
  let Bad : Set Ω := {ω | ∃ b ∈ j1NearbyIdx K,
    ∃ z ∈ laneBBlockAnnulus i (T20.dyCenter K b) K,
      5 * Real.log s < |phiMN W P 0 K z ω -
        phiMN W P 0 K (T20.dyCenter K b) ω|}
  let BadAll : Set Ω := {ω | ∃ j : Bool, ∃ b ∈ j1NearbyIdx K,
    ∃ z ∈ laneBBlockAnnulus j (T20.dyCenter K b) K,
      5 * Real.log s < |phiMN W P 0 K z ω -
        phiMN W P 0 K (T20.dyCenter K b) ω|}
  have hBad : P Bad ≤ ENNReal.ofReal
      (C * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σ))) := by
    have hreal := hosc P W hW K hK (Real.log s)
      (Real.log_pos (by linarith [hs])).le
    have hAll : P BadAll ≤ ENNReal.ofReal
        (C * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σ))) :=
      j1_prob_le_of_real_le P BadAll hreal
    exact (measure_mono (by
      rintro ω ⟨b, hb, z, hz, hh⟩
      exact ⟨i, b, hb, z, hz, hh⟩)).trans hAll
  let E : ℤ × ℤ → Set Ω := fun b =>
    {ω | crossLenIn ξ (fun z => phiMN W P K n z ω)
      (laneBBlockAnnulus i (T20.dyCenter K b) K)
      (j1BlockInner i (T20.dyCenter K b) K)
      (j1BlockOuter i (T20.dyCenter K b) K) <
      ENNReal.ofReal r * ENNReal.ofReal (s⁻¹ * L)}
  have hFineNear : P {ω | ∃ b ∈ j1NearbyIdx K, ω ∈ E b} ≤ A :=
    (j1_nearby_union_le_near_union P K E).trans hFine
  have hth :
      ENNReal.ofReal (Real.exp (|ξ| * (5 * Real.log s))) *
        ENNReal.ofReal (T⁻¹ * (r * L)) =
      ENNReal.ofReal r * ENNReal.ofReal (s⁻¹ * L) := by
    have he : |ξ| * (5 * Real.log s) =
        |ξ| * 5 * Real.log s := by ring
    rw [he]
    exact j1_coarse_scaled_lower_threshold ξ 5 T r L
      (by norm_num) hT (by dsimp [r]; positivity)
  have htr := (j1_nearby_small_full_field_transfer
    P W hW ξ hKn i (5 * Real.log s)
    (ENNReal.ofReal (T⁻¹ * (r * L)))
    (ENNReal.ofReal (s * (r * L)))).1
  rw [hth] at htr
  calc
    P {ω | ∃ b ∈ j1NearbyIdx K,
      ENNReal.ofReal
        (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
        crossLenIn ξ (fun z => phiMN W P 0 n z ω)
          (laneBBlockAnnulus i (T20.dyCenter K b) K)
          (j1BlockInner i (T20.dyCenter K b) K)
          (j1BlockOuter i (T20.dyCenter K b) K) <
        ENNReal.ofReal (T⁻¹ * (r * L))} ≤
      P {ω | ∃ b ∈ j1NearbyIdx K, ω ∈ E b} + P Bad := htr
    _ ≤ A + ENNReal.ofReal
        (C * 4 ^ K * Real.exp (-(Real.log s)^2 / (2 * σ))) :=
      add_le_add hFineNear hBad

end SupercriticalLQGUniqueness.B2.DG20Conc

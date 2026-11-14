/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1NearRoundOsc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearbyIdx
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundShapes
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLargeAnnulusOsc

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Metric Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_round_outer_radius_eq {K m : ℕ} (hmK : m ≤ K) :
    2 * LaneCInputs.sourceRadius K m =
      (2 : ℝ) ^ (m + 1) * (2 : ℝ)⁻¹ ^ K := by
  rw [← j1_round_radius_eq hmK, pow_succ]
  ring

theorem j1_nearby_round_oscillation_bad_event :
    ∃ C σ : ℝ, 0 < C ∧ 0 < σ ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (K m : ℕ) (hmK : m + 1 ≤ K)
      (x : ℝ) (hx : 0 ≤ x),
      P.real {ω | ∃ b ∈ j1NearbyIdx K,
        ∃ z ∈ j1SourceCross K m b,
          (2 : ℝ) ^ (m + 1) * x <
            |phiMN W P 0 K z ω -
              phiMN W P 0 K (T20.dyCenter K b) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ)) := by
  obtain ⟨C, σ, hC, hσ, htail⟩ :=
    j1_phiMN_nearby_oscillation_bad_event
  refine ⟨C, σ, hC, hσ, ?_⟩
  intro Ω _ P W hW K m hmK x hx
  let A : {b // b ∈ j1NearbyIdx K} → Set ℂ :=
    fun b => j1SourceCross K m b.1
  let v : {b // b ∈ j1NearbyIdx K} → ℂ :=
    fun b => T20.dyCenter K b.1
  have hr : 2 * LaneCInputs.sourceRadius K m ≤ 1 := by
    simpa only [LaneCInputs.sourceRadius] using
      (laneB_large_radius_le_one hmK)
  have hrad : 2 * LaneCInputs.sourceRadius K m ≤
      (2 : ℝ) ^ (m + 1) * (2 : ℝ)⁻¹ ^ K :=
    (j1_round_outer_radius_eq (by omega : m ≤ K)).le
  have h := htail hW K A v
    (2 * LaneCInputs.sourceRadius K m) ((2 : ℝ) ^ (m + 1)) x
    hr (by positivity) hx hrad
    (fun b => j1_nearbyIdx_center b.2)
    (by
      intro b z hz
      change dist z (T20.dyCenter K b.1) ∈
        Icc (LaneCInputs.sourceRadius K m)
          (2 * LaneCInputs.sourceRadius K m) at hz
      exact mem_closedBall.mpr hz.2)
  have hevent :
      {ω | ∃ b ∈ j1NearbyIdx K,
        ∃ z ∈ j1SourceCross K m b,
          (2 : ℝ) ^ (m + 1) * x <
            |phiMN W P 0 K z ω -
              phiMN W P 0 K (T20.dyCenter K b) ω|} =
      {ω | ∃ b, ∃ z ∈ A b,
        (2 : ℝ) ^ (m + 1) * x <
          |phiMN W P 0 K z ω -
            phiMN W P 0 K (v b) ω|} := by
    ext ω
    constructor
    · rintro ⟨b, hb, z, hz, hbad⟩
      exact ⟨⟨b, hb⟩, z, hz, hbad⟩
    · rintro ⟨⟨b, hb⟩, z, hz, hbad⟩
      exact ⟨b, hb, z, hz, hbad⟩
  rw [hevent]
  exact h

end SupercriticalLQGUniqueness.B2.DG20Conc

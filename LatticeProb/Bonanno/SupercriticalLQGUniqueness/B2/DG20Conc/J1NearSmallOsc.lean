/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.J1NearSmallOsc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1NearbyIdx
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusOsc

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem j1_nearby_small_oscillation_bad_event :
    ∃ C σ : ℝ, 0 < C ∧ 0 < σ ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
      (K : ℕ) (hK : 3 ≤ K) (x : ℝ) (hx : 0 ≤ x),
      P.real {ω | ∃ i : Bool, ∃ b ∈ j1NearbyIdx K,
        ∃ z ∈ laneBBlockAnnulus i (T20.dyCenter K b) K,
          5 * x < |phiMN W P 0 K z ω -
            phiMN W P 0 K (T20.dyCenter K b) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ)) := by
  obtain ⟨C, σ, hC, hσ, htail⟩ :=
    j1_phiMN_nearby_oscillation_bad_event
  refine ⟨C, σ, hC, hσ, ?_⟩
  intro Ω _ P W hW K hK x hx
  let A : Bool × {b // b ∈ j1NearbyIdx K} → Set ℂ :=
    fun j => laneBBlockAnnulus j.1 (T20.dyCenter K j.2.1) K
  let v : Bool × {b // b ∈ j1NearbyIdx K} → ℂ :=
    fun j => T20.dyCenter K j.2.1
  have h := htail hW K A v (5 * (2 : ℝ)⁻¹ ^ K) 5 x
    (laneB_small_radius_le_one hK) (by norm_num) hx (le_refl _)
    (fun j => j1_nearbyIdx_center j.2.2)
    (fun j => laneB_block_annulus_subset_closedBall j.1
      (T20.dyCenter K j.2.1) K)
  have hevent :
      {ω | ∃ i : Bool, ∃ b ∈ j1NearbyIdx K,
        ∃ z ∈ laneBBlockAnnulus i (T20.dyCenter K b) K,
          5 * x < |phiMN W P 0 K z ω -
            phiMN W P 0 K (T20.dyCenter K b) ω|} =
      {ω | ∃ j, ∃ z ∈ A j,
        5 * x < |phiMN W P 0 K z ω -
          phiMN W P 0 K (v j) ω|} := by
    ext ω
    constructor
    · rintro ⟨i, b, hb, z, hz, hbad⟩
      exact ⟨⟨i, ⟨b, hb⟩⟩, z, hz, hbad⟩
    · rintro ⟨⟨i, ⟨b, hb⟩⟩, z, hz, hbad⟩
      exact ⟨i, b, hb, z, hz, hbad⟩
  rw [hevent]
  exact h

end SupercriticalLQGUniqueness.B2.DG20Conc

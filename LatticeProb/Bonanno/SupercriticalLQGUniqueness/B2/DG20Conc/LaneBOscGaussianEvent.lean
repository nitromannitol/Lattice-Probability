/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBOscGaussianEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBObigGaussian
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBOscillation

 





set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneB_coarse_oscillation_gaussian_bad_event :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (K : ℕ) (Y : ℂ → Ω → ℝ),
      (∀ z, (fun ω => Y z ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 z) →
      (∀ ω, ContDiff ℝ 1 fun z => Y z ω) →
    ∀ {ι : Type*} (A : ι → Set ℂ) (v : ι → ℂ) (B x : ℝ),
      0 ≤ B → 0 ≤ x →
      (∀ i, A i ⊆ T20D.bigBox) →
      (∀ i, v i ∈ T20D.bigBox) →
      (∀ i, ∀ z ∈ A i, ‖z - v i‖ ≤ B * (2 : ℝ)⁻¹ ^ K) →
      P.real {ω | ∃ i, ∃ z ∈ A i,
        B * x < |Y z ω - Y (v i) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := laneB_Obig_gaussian_tail
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW K Y hY hYc ι A v B x hB hx hA hv hrad
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hsub : {ω | ∃ i, ∃ z ∈ A i,
      B * x < |Y z ω - Y (v i) ω|} ⊆
      {ω | x ≤ T20C.Obig K Y ω} := by
    intro ω hω
    obtain ⟨i, z, hz, hbad⟩ := hω
    have hosc := laneB_coarse_oscillation_on_annuli K Y ω (hYc ω)
      A v B hA hv hrad i z hz
    by_cases hB0 : B = 0
    · subst B
      have : |Y z ω - Y (v i) ω| ≤ 0 := by simpa using hosc
      exfalso
      have : 0 < |Y z ω - Y (v i) ω| := by simpa using hbad
      linarith
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
      by_contra hnot
      have hlt : T20C.Obig K Y ω < x := lt_of_not_ge hnot
      have hmul := mul_lt_mul_of_pos_left hlt hBpos
      exfalso
      nlinarith
  have hfin : P {ω | x ≤ T20C.Obig K Y ω} ≠ ⊤ :=
    measure_ne_top_of_subset (subset_univ _) (by simp)
  exact (measureReal_mono hsub hfin).trans (htail hW K Y hY hYc x hx)

end SupercriticalLQGUniqueness.B2.DG20Conc

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPhiOscGaussianEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBOscGaussianEvent
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

 


theorem laneB_phiMN_coarse_oscillation_gaussian_bad_event :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (K : ℕ) {ι : Type*} (A : ι → Set ℂ) (v : ι → ℂ) (B x : ℝ),
      0 ≤ B → 0 ≤ x →
      (∀ i, A i ⊆ T20D.bigBox) →
      (∀ i, v i ∈ T20D.bigBox) →
      (∀ i, ∀ z ∈ A i, ‖z - v i‖ ≤ B * (2 : ℝ)⁻¹ ^ K) →
      P.real {ω | ∃ i, ∃ z ∈ A i,
        B * x < |phiMN W P 0 K z ω - phiMN W P 0 K (v i) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := laneB_coarse_oscillation_gaussian_bad_event
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW K ι A v B x hB hx hA hv hrad
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hpn : ((2 : ℝ) ^ K)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨Y, -, hYae, _, hYc, -⟩ :=
    exists_C1_modification_phi hW (a := ((2 : ℝ) ^ K)⁻¹)
      (b := 1) (by positivity) hpn
  have hvφ := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hind : ∀ᵐ ω ∂P, ∀ z, phiMN W P 0 K z ω = Y z ω :=
    T20C.ae_forall_eq_of_cont hvφ.cont (fun ω => (hYc ω).continuous) fun z =>
      (hvφ.ae_eq z).trans (by rw [inv_pow, pow_zero]; exact (hYae z).symm)
  have hnull : P {ω | ¬ ∀ z, phiMN W P 0 K z ω = Y z ω} = 0 := (ae_iff).1 hind
  have hY := htail hW K Y hYae hYc A v B x hB hx hA hv hrad
  have hsub : {ω | ∃ i, ∃ z ∈ A i,
      B * x < |phiMN W P 0 K z ω - phiMN W P 0 K (v i) ω|} ⊆
      {ω | ∃ i, ∃ z ∈ A i, B * x < |Y z ω - Y (v i) ω|} ∪
      {ω | ¬ ∀ z, phiMN W P 0 K z ω = Y z ω} := by
    intro ω hω
    by_cases heq : ∀ z, phiMN W P 0 K z ω = Y z ω
    · left
      obtain ⟨i, z, hz, hbad⟩ := hω
      exact ⟨i, z, hz, by simpa only [heq z, heq (v i)] using hbad⟩
    · exact Or.inr heq
  have hfin : P ({ω | ∃ i, ∃ z ∈ A i, B * x < |Y z ω - Y (v i) ω|} ∪
      {ω | ¬ ∀ z, phiMN W P 0 K z ω = Y z ω}) ≠ ⊤ :=
    measure_ne_top_of_subset (subset_univ _) (by simp)
  calc
    P.real {ω | ∃ i, ∃ z ∈ A i,
      B * x < |phiMN W P 0 K z ω - phiMN W P 0 K (v i) ω|}
      ≤ P.real ({ω | ∃ i, ∃ z ∈ A i, B * x < |Y z ω - Y (v i) ω|} ∪
        {ω | ¬ ∀ z, phiMN W P 0 K z ω = Y z ω}) := measureReal_mono hsub hfin
    _ ≤ P.real {ω | ∃ i, ∃ z ∈ A i, B * x < |Y z ω - Y (v i) ω|} +
        P.real {ω | ¬ ∀ z, phiMN W P 0 K z ω = Y z ω} := measureReal_union_le _ _
    _ ≤ C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
      simp only [Measure.real, hnull, ENNReal.toReal_zero, add_zero]
      exact hY

end SupercriticalLQGUniqueness.B2.DG20Conc

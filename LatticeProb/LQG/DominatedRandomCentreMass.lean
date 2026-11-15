import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma28
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail

/-! # Lower tails for locally dominated LQG ball masses -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

/-- A uniform whole-plane GMC lower-tail estimate controls the mass of a ball
at a possibly dependent random centre, under almost-sure local domination. -/
theorem measure_randomCentre_ball_mass_le_of_lqg_domination
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ → ℂ → Ω → ℝ) (ν μ : Ω → Measure ℂ) (z : Ω → ℂ)
    {γ p ρ e : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hν : MatedCRTHarmonic.GMSLemma27.IsLQGAreaOf γ H ν P)
    (hdom : ∀ᵐ ω ∂P, ∀ A : Set ℂ, MeasurableSet A →
      A ⊆ ball (0 : ℂ) 1 → ν ω A ≤ μ ω A)
    (hp : 0 < p) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (he : e < p ^ 2 / (2 * γ ^ 2) - 2) :
    ∃ C : ℝ, ∀ δ ∈ Ioo (0 : ℝ) (min 1 (1 - ρ)),
      P {ω | z ω ∈ ball (0 : ℂ) ρ ∧
        μ ω (ball (z ω) δ) ≤ ENNReal.ofReal (δ ^ (2 + γ ^ 2 / 2 + p))} ≤
        ENNReal.ofReal (C * δ ^ e) := by
  obtain ⟨C, hC⟩ := MatedCRTHarmonic.GMSLemma27.lemma28_wholePlane_strict
    (MatedCRTHarmonic.GMCFacts.gmcLowerTail_holds hγ hγ2) hγ hH hν hp hρ0 hρ1 he
  refine ⟨C, fun δ hδ => (measure_mono_ae ?_).trans (hC δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩)⟩
  filter_upwards [hdom] with ω hω hbad
  refine ⟨z ω, hbad.1, (hω _ measurableSet_ball ?_).trans hbad.2⟩
  intro y hy
  rw [mem_ball_zero_iff] at hbad ⊢
  rw [mem_ball, dist_eq_norm] at hy
  calc
    ‖y‖ = ‖(y - z ω) + z ω‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - z ω‖ + ‖z ω‖ := norm_add_le _ _
    _ < 1 := by
      have hδρ := hδ.2.trans_le (min_le_right (1 : ℝ) (1 - ρ))
      linarith [hbad.1]

end LatticeProb.LQG

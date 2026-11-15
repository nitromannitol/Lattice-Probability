import LatticeProb.LQG.LQGMeasure
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform

/-! # Identification of LQG area from spatial almost-everywhere agreement -/

set_option autoImplicit false

open MeasureTheory Filter Set

namespace LatticeProb.LQG

/-- A dyadic LQG limit identifies the area of a distribution when the circle
profiles agree almost everywhere in space at each dyadic scale. -/
theorem lqgArea_eq_of_isLQGLimit_ae {γ : ℝ} {h : LQGMetric.DistC}
    {H : ℝ → ℂ → ℝ} {μ : Measure ℂ} (hμ : IsLQGLimit γ H μ)
    (hcircle : ∀ k : ℕ, ∀ᵐ z ∂volume,
      H (dyadicScale k) z = LQGMetric.circleAvg h (dyadicScale k) z) :
    MatedCRTHarmonic.CellScaling.lqgArea γ h = μ := by
  have hs (k : ℕ) : MatedCRTHarmonic.CellScaling.dyadicScale k = dyadicScale k := by
    simp [MatedCRTHarmonic.CellScaling.dyadicScale, dyadicScale, zpow_neg, zpow_natCast]
  have ha (k : ℕ) : MatedCRTHarmonic.CellScaling.lqgAreaApprox γ h k =
      lqgApprox γ H (dyadicScale k) := by
    simp only [MatedCRTHarmonic.CellScaling.lqgAreaApprox, lqgApprox, hs]
    apply withDensity_congr_ae
    filter_upwards [hcircle k] with z hz
    rw [hz]
  apply MatedCRTHarmonic.LQGCoord.lqgArea_eq_of_isVagueLimitC
  refine ⟨?_, ?_⟩
  · let _ : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
    exact fun K hK => hK.measure_lt_top
  · intro f hf hfc
    simpa only [ha] using hμ.tendsto_integral f hf hfc

/-- The area identification holds on one event when the dyadic profiles agree
almost everywhere in space on that event. -/
theorem ae_lqgArea_eq_of_isLQGMeasure_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {h : Ω → LQGMetric.DistC}
    {H : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasure P γ H μ)
    (hcircle : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      H ω (dyadicScale k) z = LQGMetric.circleAvg (h ω) (dyadicScale k) z) :
    ∀ᵐ ω ∂P, MatedCRTHarmonic.CellScaling.lqgArea γ (h ω) = μ ω := by
  filter_upwards [hμ, hcircle] with ω hμω hcircleω
  exact lqgArea_eq_of_isLQGLimit_ae hμω hcircleω

end LatticeProb.LQG

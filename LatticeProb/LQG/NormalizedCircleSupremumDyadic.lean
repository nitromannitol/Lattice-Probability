import LatticeProb.LQG.CircleSupremumDyadic
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCUpper.CircleCover

/-! # Dyadic circle-average bounds for normalized whole-plane fields -/

open MeasureTheory Filter Set Metric

namespace LatticeProb.LQG

/-- A selected continuous circle-average version of a normalized whole-plane
GFF has an eventual dyadic spatial supremum bound on one event. -/
theorem ae_eventually_dyadic_circle_sup_le_of_normalized_gff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {c : Ω → ℝ → ℂ → ℝ}
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {δ ρ : ℝ} (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ z ∈ ball (0 : ℂ) ρ,
      |c ω (dyadicScale k) z| ≤ (2 + δ) * Real.log (dyadicScale k)⁻¹ := by
  let H : ℝ → ℂ → Ω → ℝ := fun r z ω => c ω r z
  have hH : LQGMetric.DFGPS.IsCircleAvgVersion X P H := ⟨hc, heq⟩
  have htail : MatedCRTHarmonic.GMS4b.CircleAverageSupBound P H :=
    MatedCRTHarmonic.GMCUpper.circleAverageSupBound_of_model hX hH
      (MatedCRTHarmonic.GMCUpper.circleAverageSupBoundModel_holds hX hH)
  exact ae_eventually_dyadic_circle_sup_le P H htail hδ hρ

end LatticeProb.LQG

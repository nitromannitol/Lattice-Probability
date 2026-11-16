import LatticeProb.LQG.RecentredSquareMaximalMoment

/-! # Countable-center maximal finiteness of recentred square approximations -/

open MeasureTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- For countably many centers, the supremum over approximation levels is finite
simultaneously at every square scale almost surely for the same circle-average field. -/
theorem ae_iSup_normalized_recentred_square_mass_ne_top_of_countable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (D : Set ℂ) (hD : D.Countable) :
    ∀ᵐ ω ∂P, ∀ z ∈ D, ∀ m,
      (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ≠ ⊤ := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_lintegral_iSup_normalized_recentred_square_rpow_le hH hHm hγ hγ2 hp hpq hq
  refine (ae_ball_iff hD).2 fun z _ => ae_all_iff.2 fun m => ?_
  have hr : 0 < radius m := radius_pos m
  have hε : 0 < 2 * radius m := by positivity
  have hM : ∀ k, AEMeasurable (normalizedRecentredSquareMass H γ z m k) P := by
    intro k
    exact ((measurable_recentred_square_mass hH hHm γ (2 * radius m) hε.ne' z m k).const_mul _).aemeasurable
  have hfin := ae_lt_top' ((AEMeasurable.iSup hM).pow_const p)
    (ne_top_of_le_ne_top hC.ne (hmoment z m).1)
  filter_upwards [hfin] with ω hω
  intro h
  rw [h, ENNReal.top_rpow_of_pos (by linarith : 0 < p)] at hω
  exact lt_irrefl _ hω

end LatticeProb.LQG

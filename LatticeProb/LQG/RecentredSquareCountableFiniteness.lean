import LatticeProb.LQG.RecentredSquareMaximalMoment

/-! # Countable-center finiteness of recentred square approximations -/

open MeasureTheory Set

namespace LatticeProb.LQG

/-- For countably many centers, all square scales and approximation levels are finite
simultaneously almost surely for the same circle-average field. -/
theorem ae_normalized_recentred_square_mass_ne_top_of_countable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) (D : Set ℂ) (hD : D.Countable) :
    ∀ᵐ ω ∂P, ∀ z ∈ D, ∀ m k,
      normalizedRecentredSquareMass H γ z m k ω ≠ ⊤ := by
  obtain ⟨_, _, h⟩ :=
    exists_lintegral_iSup_normalized_recentred_square_rpow_le hH hHm hγ hγ2 hp hpq hq
  exact (ae_ball_iff hD).2 fun z _ => ae_all_iff.2 fun m => (h z m).2

end LatticeProb.LQG

import LatticeProb.LQG.RecentredSquareMaximalMoment

/-! # Finite-center maximal moments of recentred square approximations -/

open MeasureTheory
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- A single finite constant controls the maximal moment over any finite set of centers.
The finite supremum is zero when the set of centers is empty. -/
theorem exists_lintegral_finset_sup_iSup_normalized_recentred_square_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (S : Finset ℂ) (m : ℕ),
      (∫⁻ ω, (S.sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p ∂P)
        ≤ (S.card : ℝ≥0∞) * C := by
  classical
  obtain ⟨C, hC, hmoment⟩ :=
    exists_lintegral_iSup_normalized_recentred_square_rpow_le hH hHm hγ hγ2 hp hpq hq
  refine ⟨C, hC, fun S m => ?_⟩
  have hp0 : 0 < p := by linarith
  have hmeas : ∀ z ∈ S, AEMeasurable
      (fun ω => (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p) P := by
    intro z _
    have hr : 0 < radius m := radius_pos m
    have hε : 0 < 2 * radius m := by positivity
    have hM : ∀ k, AEMeasurable (normalizedRecentredSquareMass H γ z m k) P := by
      intro k
      exact ((measurable_recentred_square_mass hH hHm γ (2 * radius m) hε.ne' z m k).const_mul _).aemeasurable
    exact (AEMeasurable.iSup hM).pow_const p
  calc
    (∫⁻ ω, (S.sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p ∂P)
        ≤ ∫⁻ ω, ∑ z ∈ S, (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          apply Finset.apply_sup_le_sum (f := fun x : ℝ≥0∞ => x ^ p) (ENNReal.zero_rpow_of_pos hp0)
          intro a b
          rw [(show Monotone (fun x : ℝ≥0∞ => x ^ p) from
            fun _ _ h => ENNReal.rpow_le_rpow h hp0.le).map_sup]
          exact sup_le (self_le_add_right _ _) (self_le_add_left _ _)
    _ = ∑ z ∈ S, ∫⁻ ω, (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p ∂P :=
      lintegral_finsetSum' S hmeas
    _ ≤ ∑ _z ∈ S, C := Finset.sum_le_sum fun z _ => (hmoment z m).1
    _ = (S.card : ℝ≥0∞) * C := by simp

end LatticeProb.LQG

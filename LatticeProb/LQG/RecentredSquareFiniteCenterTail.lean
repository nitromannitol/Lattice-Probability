import LatticeProb.LQG.RecentredSquareFiniteCenterMoment

/-! # Finite-center maximal tails of recentred square approximations -/

open MeasureTheory
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- The maximal mass over finitely many centers and all levels has a uniform power tail.
The supremum over the empty set of centers is zero. -/
theorem exists_measure_finset_sup_iSup_normalized_recentred_square_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (S : Finset ℂ) (m : ℕ) (t : ℝ), 0 < t →
      MeasurableSet {ω | ENNReal.ofReal t ≤
        S.sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω} ∧
      P {ω | ENNReal.ofReal t ≤
        S.sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω} ≤
        (S.card : ℝ≥0∞) * C / ENNReal.ofReal (t ^ p) := by
  classical
  obtain ⟨C, hC, hmoment⟩ :=
    exists_lintegral_finset_sup_iSup_normalized_recentred_square_rpow_le hH hHm hγ hγ2 hp hpq hq
  refine ⟨C, hC, fun S m t ht => ?_⟩
  have hp0 : 0 < p := by linarith
  have hM : ∀ z, Measurable (fun ω => ⨆ k, normalizedRecentredSquareMass H γ z m k ω) := by
    intro z
    have hε : 0 < 2 * radius m := by have := radius_pos m; positivity
    exact Measurable.iSup fun k =>
      (measurable_recentred_square_mass hH hHm γ (2 * radius m) hε.ne' z m k).const_mul _
  have hS : Measurable (fun ω => S.sup fun z => ⨆ k,
      normalizedRecentredSquareMass H γ z m k ω) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert z S hz ih =>
      simpa only [Finset.sup_insert] using (hM z).max ih
  refine ⟨measurableSet_le measurable_const hS, ?_⟩
  have htpos : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hsub : {ω | ENNReal.ofReal t ≤
      S.sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω} ⊆
      {ω | ENNReal.ofReal (t ^ p) ≤
        (S.sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p} := by
    intro ω hω
    have h := ENNReal.rpow_le_rpow hω hp0.le
    rwa [ENNReal.ofReal_rpow_of_nonneg ht.le hp0.le] at h
  calc
    _ ≤ P {ω | ENNReal.ofReal (t ^ p) ≤
        (S.sup fun z => ⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, (S.sup fun z => ⨆ k,
        normalizedRecentredSquareMass H γ z m k ω) ^ p ∂P) / ENNReal.ofReal (t ^ p) :=
      meas_ge_le_lintegral_div (hS.aemeasurable.pow_const p)
        (ENNReal.ofReal_pos.mpr htpos).ne' ENNReal.ofReal_ne_top
    _ ≤ _ := ENNReal.div_le_div_right (hmoment S m) _

end LatticeProb.LQG

import LatticeProb.LQG.RecentredSquareMoment
import Mathlib.Analysis.MeanInequalitiesPow

/-! # Positive moments of recentred square increments -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper

namespace LatticeProb.LQG

/-- The mass of a recentred square approximation is measurable in the sample. -/
theorem measurable_recentred_square_mass {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ ε : ℝ) (hε : ε ≠ 0)
    (z : ℂ) (m k : ℕ) :
    Measurable (fun ω => lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
      (radius (m + k) / ε) (sqQ (sqCorner z (radius m)) m)) := by
  have hr : 0 < radius (m + k) := radius_pos _
  have hjm := measurable_uncurry_coord hH hHm hr
  have hd : Measurable fun p : ℂ × Ω => nDens γ H z ε (radius (m + k)) p.1 p.2 :=
    ENNReal.measurable_ofReal.comp (((hjm.sub ((hHm ε z).comp measurable_snd)).const_mul
      γ).exp.const_mul _)
  simp_rw [lqgApprox_rescale_recentred_eq_lintegral H _ γ z hε _ (measurableSet_sqQ _ _)]
  exact hd.lintegral_prod_left'

/-- Uniform positive moments of the normalized difference between consecutive
recentred square masses. Both levels use the same circle-average process. -/
theorem exists_lintegral_recentred_square_increment_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q : ℝ}
    (hγ : 0 < γ) (hq1 : 1 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (ε : ℝ) (m k : ℕ), 0 < ε →
      radius m ≤ ε / 2 → ε / 8 < radius m →
      ∫⁻ ω, (ENNReal.ofReal (ε⁻¹ ^ 2) * ENNReal.ofReal
        |(lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
          (radius (m + k) / ε) (sqQ (sqCorner z (radius m)) m)).toReal -
         (lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
          (radius (m + (k + 1)) / ε) (sqQ (sqCorner z (radius m)) m)).toReal|) ^ q ∂P ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_lintegral_recentred_square_rpow_le hH hHm hγ hq1 hq
  refine ⟨(2 : ℝ≥0∞) ^ (q - 1) * (C + C), ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) (by simp))
      (ENNReal.add_lt_top.mpr ⟨hC, hC⟩)
  intro z ε m k hε hupper hlower
  let X : ℕ → Ω → ℝ≥0∞ := fun j ω => lqgApprox γ
    (fun s w => H (ε * s) w ω - H ε z ω)
    (radius (m + j) / ε) (sqQ (sqCorner z (radius m)) m)
  let a : ℝ≥0∞ := ENNReal.ofReal (ε⁻¹ ^ 2)
  have hm : ∀ j, Measurable (X j) := fun j =>
    measurable_recentred_square_mass hH hHm γ ε hε.ne' z m j
  have hp (ω : Ω) : a * ENNReal.ofReal |(X k ω).toReal - (X (k + 1) ω).toReal| ≤
      a * X k ω + a * X (k + 1) ω := by
    rw [← mul_add]
    apply mul_le_mul' le_rfl
    calc ENNReal.ofReal |(X k ω).toReal - (X (k + 1) ω).toReal|
        ≤ ENNReal.ofReal ((X k ω).toReal + (X (k + 1) ω).toReal) := by
          apply ENNReal.ofReal_le_ofReal
          have hx : 0 ≤ (X k ω).toReal := ENNReal.toReal_nonneg
          have hy : 0 ≤ (X (k + 1) ω).toReal := ENNReal.toReal_nonneg
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ ≤ ENNReal.ofReal (X k ω).toReal + ENNReal.ofReal (X (k + 1) ω).toReal :=
          ENNReal.ofReal_add_le
      _ ≤ X k ω + X (k + 1) ω := add_le_add ENNReal.ofReal_toReal_le ENNReal.ofReal_toReal_le
  change ∫⁻ ω, (a * ENNReal.ofReal |(X k ω).toReal - (X (k + 1) ω).toReal|) ^ q ∂P ≤ _
  calc
    _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (q - 1) * ((a * X k ω) ^ q + (a * X (k + 1) ω) ^ q) ∂P :=
      lintegral_mono fun ω => (ENNReal.rpow_le_rpow (hp ω) (by linarith)).trans
        (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq1.le)
    _ = (2 : ℝ≥0∞) ^ (q - 1) *
        ((∫⁻ ω, (a * X k ω) ^ q ∂P) + ∫⁻ ω, (a * X (k + 1) ω) ^ q ∂P) := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)),
        lintegral_add_left' (((hm k).const_mul a).pow_const q).aemeasurable]
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add (hbound z ε m k hε hupper hlower)
      (hbound z ε m (k + 1) hε hupper hlower))

end LatticeProb.LQG

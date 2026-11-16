import LatticeProb.LQG.RecentredSquareNormalizedIncrement
import LatticeProb.LQG.RecentredSquareIncrementMoment
import LatticeProb.Bonanno.QuantumZipper.Proofs.GMC.BdryMomentsSup

/-! # Maximal moments of recentred square approximations -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC LQGMetric.DGMC.Neg3
open QuantumZipper QuantumZipper.AreaP3b

namespace LatticeProb.LQG

/-- The square mass normalized at the square scale. -/
noncomputable def normalizedRecentredSquareMass {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ)
    (γ : ℝ) (z : ℂ) (m k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * radius m)⁻¹ ^ 2) *
    lqgApprox γ (fun s w => H (2 * radius m * s) w ω - H (2 * radius m) z ω)
      (radius (m + k) / (2 * radius m)) (sqQ (sqCorner z (radius m)) m)

/-- Uniform finite maximal moments for normalized square approximations of the same field.
For each center and scale, every level is finite almost surely. -/
theorem exists_lintegral_iSup_normalized_recentred_square_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}
    (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ p q : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp : 1 < p) (hpq : p < q)
    (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (m : ℕ),
      (∫⁻ ω, (⨆ k, normalizedRecentredSquareMass H γ z m k ω) ^ p ∂P) ≤ C ∧
      ∀ᵐ ω ∂P, ∀ k, normalizedRecentredSquareMass H γ z m k ω ≠ ⊤ := by
  let : IsProbabilityMeasure P := hH.isProbabilityMeasure
  have hq1 : 1 < q := lt_trans hp hpq
  obtain ⟨A, hA, hmoment⟩ := exists_lintegral_recentred_square_rpow_le hH hHm hγ hq1 hq
  let B : ℝ≥0∞ := ENNReal.ofReal (cRate γ 0 (1 / 4))
  let ρ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(min
    (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
    ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log 2)))
  have hB : B ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ : ρ < 1 := ENNReal.ofReal_lt_one.mpr (recentred_square_increment_rate_mem γ hγ hγ2).2
  refine ⟨QuantumZipper.GMCMoments.supMomConst p q A B ρ,
    lt_top_iff_ne_top.mpr (QuantumZipper.GMCMoments.supMomConst_ne_top hp.le hpq hA.ne hB hρ), ?_⟩
  intro z m
  have hr : 0 < radius m := radius_pos m
  have hε : 0 < 2 * radius m := by positivity
  have hupper : radius m ≤ (2 * radius m) / 2 := by linarith
  have hlower : (2 * radius m) / 8 < radius m := by linarith
  have hM : ∀ k, AEMeasurable (normalizedRecentredSquareMass H γ z m k) P := by
    intro k
    exact ((measurable_recentred_square_mass hH hHm γ (2 * radius m) hε.ne' z m k).const_mul _).aemeasurable
  have hqA : ∀ k, ∫⁻ ω, normalizedRecentredSquareMass H γ z m k ω ^ q ∂P ≤ A := by
    intro k
    exact hmoment z (2 * radius m) m k hε hupper hlower
  have hinc : ∀ k, ∫⁻ ω, QuantumZipper.GMCMoments.incr
      (normalizedRecentredSquareMass H γ z m) k ω ∂P ≤ B * ρ ^ k := by
    intro k
    exact lintegral_normalized_recentred_square_increment_le hH hHm hγ hγ2 z m k
  exact ⟨QuantumZipper.GMCMoments.lintegral_iSup_rpow_le_supMomConst hM hp.le hpq hA.ne hqA hinc,
    QuantumZipper.GMCMoments.ae_ne_top_of_lintegral_rpow hM (by linarith) hA.ne hqA⟩

end LatticeProb.LQG

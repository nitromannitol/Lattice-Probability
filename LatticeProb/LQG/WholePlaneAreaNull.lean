import LatticeProb.LQG.MarkedRootingMeasurableSet

/-! # Fixed null sets for whole-plane quantum area -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.Gauss

/-- A fixed Lebesgue-null Borel subset of the unit disk has zero quantum area almost surely. -/
theorem IsWholePlaneGFF.ae_lqgMeasure_eq_zero_of_volume_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {μ : Ω → Measure ℂ} (hμ : LQG.IsLQGMeasure P γ hcirc μ)
    {A : Set ℂ} (hA : MeasurableSet A) (hA0 : volume A = 0)
    (hAsub : A ⊆ Metric.ball (0 : ℂ) 1) :
    ∀ᵐ ω ∂P, μ ω A = 0 := by
  let S : Set (ℂ × (Fin 0 → ℝ)) := A ×ˢ univ
  have hS : MeasurableSet S := hA.prod MeasurableSet.univ
  have hroot := hh.lintegral_lqgMeasure_marked_eq_of_measurableSet hγ0 hγ2 hμ
    (m := 0) (φ := fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hS
  have hleft : ∀ ω, (∫⁻ z in Metric.ball (0 : ℂ) 1,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun i => hC ω (Fin.elim0 i)) ∂(μ ω)) =
      μ ω A := by
    intro ω
    have heq : (∫⁻ z in Metric.ball (0 : ℂ) 1,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (z, fun i => hC ω (Fin.elim0 i)) ∂(μ ω)) =
        ∫⁻ z in Metric.ball (0 : ℂ) 1, A.indicator (fun _ => (1 : ℝ≥0∞)) z ∂(μ ω) := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ A <;> simp [S, hz]
    rw [heq]
    change (∫⁻ z, A.indicator (1 : ℂ → ℝ≥0∞) z ∂((μ ω).restrict (Metric.ball 0 1))) = μ ω A
    rw [lintegral_indicator_one hA, Measure.restrict_apply hA, inter_eq_left.mpr hAsub]
  have hzero : (∫⁻ ω, μ ω A ∂P) = 0 := by
    simp_rw [← hleft]
    rw [hroot.2]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hA0)] with z hz
    simp [S, hz]
  have hmeas : AEMeasurable (fun ω => μ ω A) P := by
    simpa only [hleft] using hroot.1
  exact (lintegral_eq_zero_iff' hmeas).mp hzero

end LatticeProb.Gauss

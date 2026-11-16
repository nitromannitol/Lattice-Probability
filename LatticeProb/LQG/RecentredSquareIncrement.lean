import LatticeProb.LQG.RecentredSquareMoment
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6B

/-! # Increments of recentred circle-average approximations -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.LQG

open MatedCRTHarmonic.GMCFacts LQGMetric.DGMC.Neg3
open MatedCRTHarmonic.MoTPort
open QuantumZipper

/-- The abstract two-radius mass is the same recentred approximation, with
physical regularization radius `radius k`. -/
theorem lqgApprox_rescale_recentred_eq_massU {Ω : Type*}
    (H : ℝ → ℂ → Ω → ℝ) (ω : Ω) (γ : ℝ) (z : ℂ)
    {ε : ℝ} (hε : ε ≠ 0) (k : ℕ) {S : Set ℂ} (hS : MeasurableSet S) :
    lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω) (radius k / ε) S =
      ConeArea6.massU γ S ε k (fun j w ω => H (radius j) w ω - H ε z ω) ω := by
  rw [lqgApprox_rescale_recentred_eq_lintegral H ω γ z hε (radius k) hS]
  rfl

/-- The two-radius increment estimate transfers to the same recentred
approximations, under its two explicit level hypotheses. -/
theorem integral_abs_recentred_increment_le_rate {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (H : ℝ → ℂ → Ω → ℝ)
    {γ ε K V : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hε : 0 < ε)
    (z : ℂ) {S : Set ℂ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    (hV : 0 ≤ V) (hSle : volume.real S ≤ V * ε ^ 2) (k : ℕ)
    (h : ConeArea6.LevelHyp P S ε K
      (fun j w ω => H (radius j) w ω - H ε z ω) k)
    (h1 : ConeArea6.LevelHyp P S ε K
      (fun j w ω => H (radius j) w ω - H ε z ω) (k + 1)) :
    ∫ ω, |(lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
          (radius k / ε) S).toReal -
        (lqgApprox γ (fun s w => H (ε * s) w ω - H ε z ω)
          (radius (k + 1) / ε) S).toReal| ∂P ≤
      QuantumZipper.AreaP3b.cRate γ K V * ε ^ 2 *
        Real.exp (-(min (2 - γ ^ 2 + (max 0 ((3 * γ - 2) / 2)) ^ 2 / 2)
          ((2 - γ) ^ 2 / 4)) * (1 / 2 * Real.log (ε / radius k))) := by
  simpa only [lqgApprox_rescale_recentred_eq_massU H _ γ z hε.ne' _ hS] using
    ConeArea6.integral_abs_massU_step_le_rate hγ hγ2 hε hS hSf hV hSle h h1

end LatticeProb.LQG

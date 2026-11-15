import LatticeProb.Prob.FirstHitCanonicalTrace
import LatticeProb.Prob.FirstHitRandomRoot

/-! # First-hit rooted paths at nonnegative times -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- Restrict the centered first-hit curve to nonnegative times. -/
noncomputable def firstHitNonnegativeCurve (c : C(ℝ, ℂ)) (z : ℂ) :
    C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) :=
  (firstHitCenteredCurve c z).comp ⟨fun t => (t : ℝ), NNReal.continuous_coe⟩

/-- Restriction of the centered first-hit curve is jointly measurable. -/
theorem measurable_firstHitNonnegativeCurve :
    Measurable fun p : C(ℝ, ℂ) × ℂ => firstHitNonnegativeCurve p.1 p.2 := by
  exact (ContinuousMap.continuous_precomp ⟨fun t : ℝ≥0 => (t : ℝ), NNReal.continuous_coe⟩).measurable.comp
    measurable_firstHitCenteredCurve

/-- The failure event of the original first-hit trace has the same measure as
that of the restricted centered curve. -/
theorem measure_firstHit_failure_eq_restricted
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : Ω → C(ℝ, ℂ)) (z : ℂ)
    (hproper : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ))
    (R a : ℝ) :
    P {ω | ¬ ∃ w, ball w a ⊆ (c ω) '' Icc
      (MatedCRTHarmonic.GMS4b.hitTime (c ω) z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧
        c ω t ∉ ball z R})} =
    P {ω | ¬ ∃ w, ball w a ⊆
      (fun t : ℝ => firstHitNonnegativeCurve (c ω) z t.toNNReal) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ firstHitNonnegativeCurve (c ω) z t.toNNReal ∉ ball 0 R})} := by
  apply measure_firstHit_failure_eq_nonnegativeTrace P (fun ω => c ω)
    (fun ω => firstHitCenteredCurve (c ω) z)
    (fun ω => firstHitNonnegativeCurve (c ω) z) z R a
  filter_upwards [hproper] with ω hω
  exact ⟨(c ω).continuous, hω, fun _ => rfl, fun _ => rfl⟩

end LatticeProb

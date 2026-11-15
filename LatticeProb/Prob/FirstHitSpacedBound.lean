import LatticeProb.Prob.FirstHitSpacedExitTrial

/-! # Conditional spaced exit bound for first-hit traces -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A bound for the restricted path transfers to the first-hit trace. -/
theorem measureReal_firstHit_failure_le_of_restricted
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : Ω → C(ℝ, ℂ)) (z : ℂ)
    (hproper : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ))
    (R a B : ℝ)
    (hbound : P.real {ω | ¬ ∃ w, ball w a ⊆
      (fun t : ℝ => firstHitNonnegativeCurve (c ω) z t.toNNReal) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ firstHitNonnegativeCurve (c ω) z t.toNNReal ∉ ball 0 R})} ≤ B) :
    P.real {ω | ¬ ∃ w, ball w a ⊆ (c ω) '' Icc
      (MatedCRTHarmonic.GMS4b.hitTime (c ω) z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧
        c ω t ∉ ball z R})} ≤ B := by
  rw [Measure.real, measure_firstHit_failure_eq_restricted P c z hproper R a]
  exact hbound

/-- A canonical path-law failure bound transfers to the first-hit trace. -/
theorem measureReal_firstHit_failure_le_of_map
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : Ω → C(ℝ, ℂ)) (hc : Measurable c) (z : ℂ)
    (hproper : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ))
    (R a B : ℝ)
    (hbound : (P.map (fun ω => firstHitNonnegativeCurve (c ω) z)).real
      {w | ¬ ∃ y, ball y a ⊆ (fun t : ℝ => w t.toNNReal) '' Icc 0
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 R})} ≤ B) :
    P.real {ω | ¬ ∃ w, ball w a ⊆ (c ω) '' Icc
      (MatedCRTHarmonic.GMS4b.hitTime (c ω) z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧
        c ω t ∉ ball z R})} ≤ B := by
  have hΦ : Measurable (fun ω => firstHitNonnegativeCurve (c ω) z) := by
    change Measurable ((fun q : C(ℝ, ℂ) × ℂ => firstHitNonnegativeCurve q.1 q.2) ∘
      (fun ω : Ω => (c ω, z)))
    exact measurable_firstHitNonnegativeCurve.comp (hc.prodMk measurable_const)
  apply measureReal_firstHit_failure_le_of_restricted P c z hproper R a
  refine le_trans ?_ hbound
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact Measure.le_map_apply (μ := P) hΦ.aemeasurable
    {w | ¬ ∃ y, ball y a ⊆ (fun t : ℝ => w t.toNNReal) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 R})}

end LatticeProb

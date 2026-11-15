import LatticeProb.Prob.FirstHitExplorationBound

/-! # Exit-segment bounds from general exploration histories -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A conditional exit-segment bound given a history containing the stopped
path descends to the stopped-path history under the path law. -/
theorem condExp_unit_exit_segment_of_history
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (W : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hW : Measurable W)
    {H : MeasurableSpace Ω} (hH : H ≤ mΩ)
    (hO : MeasurableSpace.comap (fun ω => stoppedPath
      (openExitTime (fun t (_ : Unit) => W ω t) (ball 0 1) ()) (W ω))
      inferInstance ≤ H) (q η p : ℝ) :
    let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
      ∃ y, ball y (η * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
    let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
      (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
    (∀ᵐ ω ∂P, p ≤ P[fun ω => A.indicator (fun _ => (1 : ℝ)) (W ω) | H] ω) →
    ∀ᵐ w ∂((@Measure.map Ω _ mΩ _ W P)), p ≤ ((@Measure.map Ω _ mΩ _ W P))[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap O inferInstance] w := by
  let : MeasurableSpace Ω := mΩ
  dsimp only
  intro hp
  let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
    ∃ y, ball y (η * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
  let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
    (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
  have hOm : Measurable O := measurable_stoppedPath_openExitTime measurable_id isOpen_ball
  have hA : MeasurableSet A :=
    measurableSet_real_exit_segment_contains_ball measurable_id _ _ isOpen_ball isOpen_ball _
  have hG : MeasurableSpace.comap O inferInstance ≤
      (inferInstance : MeasurableSpace (C(ℝ≥0, EuclideanSpace ℝ (Fin d)))) := hOm.comap_le
  have hGH : MeasurableSpace.comap W (MeasurableSpace.comap O inferInstance) ≤ H := by
    rw [MeasurableSpace.comap_comp]
    exact hO
  have hf : Integrable (A.indicator (fun _ => (1 : ℝ))) ((@Measure.map Ω _ mΩ _ W P)) :=
    (integrable_const (1 : ℝ)).indicator hA
  exact condExp_const_le_map_of_larger_history P W hW hG hGH hH _ hf p hp

/-- A general stopped-path exploration history with a conditional exit-segment
estimate yields the first-hit failure bound. -/
theorem measureReal_firstHit_failure_le_of_history
    {γ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    {H : MeasurableSpace Ω} (hH : H ≤ mΩ)
    (hO : let W := fun ω => firstHitNonnegativeCurve (ηL ω) 0
      MeasurableSpace.comap (fun ω => stoppedPath
        (openExitTime (fun t (_ : Unit) => W ω t) (ball 0 1) ()) (W ω))
        inferInstance ≤ H)
    (R C ε ηsize : ℝ) (hR : 0 < R) (hCpos : 0 < C) (hε : 0 < ε)
    (hηC : 2 ≤ ηsize * C) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (href : ∀ q : ℝ, 0 < q → q < 1 →
      let W := fun ω => firstHitNonnegativeCurve (ηL ω) 0
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
        ∃ y, ball y (ηsize * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      ∀ᵐ ω ∂P, p ≤ P[fun ω => A.indicator (fun _ => (1 : ℝ)) (W ω) | H] ω) :
    P.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ (ηL ω) '' Icc
      (MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0 ≤ t ∧
        ηL ω t ∉ ball 0 R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  let : MeasurableSpace Ω := mΩ
  have hm : Measurable (fun ω => firstHitNonnegativeCurve (ηL ω) 0) := by
    change Measurable ((fun q : C(ℝ, ℂ) × ℂ => firstHitNonnegativeCurve q.1 q.2) ∘
      (fun ω : Ω => (ηL ω, (0 : ℂ))))
    exact measurable_firstHitNonnegativeCurve.comp
      (hC.measurable_curves.1.prodMk measurable_const)
  apply measureReal_firstHit_failure_le_of_matingOfTrees_reference hC R C ε ηsize
    hR hCpos hε hηC hp0 hp1
  intro q hq hq1
  exact condExp_unit_exit_segment_of_history P _ hm (H := H) hH hO q ηsize p (href q hq hq1)

end LatticeProb

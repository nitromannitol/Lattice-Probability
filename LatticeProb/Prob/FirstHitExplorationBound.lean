import LatticeProb.Prob.ExplorationCanonicalBound
import LatticeProb.Prob.FirstHitReferenceExitBound

/-! # Exit-segment bounds with an augmented stopped observation -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A conditional exit-segment bound given the stopped path and an additional
measurable observation descends to the stopped-path history on its path law. -/
theorem condExp_unit_exit_segment_of_augmented_observation
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ}
    (W : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hW : Measurable W)
    (Yobs : Ω → Y) (hY : Measurable Yobs) (q η p : ℝ) :
    let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
      ∃ y, ball y (η * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
        (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
    let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
      (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
    (∀ᵐ ω ∂P, p ≤ P[fun ω => A.indicator (fun _ => (1 : ℝ)) (W ω) |
      MeasurableSpace.comap (fun ω => (O (W ω), Yobs ω)) inferInstance] ω) →
    ∀ᵐ w ∂(P.map W), p ≤ (P.map W)[A.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap O inferInstance] w := by
  dsimp only
  intro hp
  let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
    ∃ y, ball y (η * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
  let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
    (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
  have hO : Measurable O := measurable_stoppedPath_openExitTime measurable_id isOpen_ball
  have hA : MeasurableSet A :=
    measurableSet_real_exit_segment_contains_ball measurable_id _ _ isOpen_ball isOpen_ball _
  have hpair : Measurable (fun ω => (O (W ω), Yobs ω)) := (hO.comp hW).prodMk hY
  have hG : MeasurableSpace.comap O inferInstance ≤
      (inferInstance : MeasurableSpace (C(ℝ≥0, EuclideanSpace ℝ (Fin d)))) := hO.comap_le
  have hGH : MeasurableSpace.comap W (MeasurableSpace.comap O inferInstance) ≤
      MeasurableSpace.comap (fun ω => (O (W ω), Yobs ω)) inferInstance := by
    rw [MeasurableSpace.comap_comp]
    change _ ≤ MeasurableSpace.comap (fun ω => (O (W ω), Yobs ω))
      (MeasurableSpace.prod _ _)
    rw [MeasurableSpace.comap_prodMk]
    exact le_sup_left
  have hf : Integrable (A.indicator (fun _ => (1 : ℝ))) (P.map W) :=
    (integrable_const (1 : ℝ)).indicator hA
  exact condExp_const_le_map_of_larger_history P W hW hG hGH hpair.comap_le _ hf p hp

/-- An augmented stopped-path conditional estimate bounds the origin first-hit
exit trace under a mating-of-trees coupling. -/
theorem measureReal_firstHit_failure_le_of_augmented_observation
    {γ : ℝ} {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (Yobs : Ω → Y) (hY : Measurable Yobs)
    (R C ε ηsize : ℝ) (hR : 0 < R) (hCpos : 0 < C) (hε : 0 < ε)
    (hηC : 2 ≤ ηsize * C) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (href : ∀ q : ℝ, 0 < q → q < 1 →
      let W := fun ω => firstHitNonnegativeCurve (ηL ω) 0
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
        ∃ y, ball y (ηsize * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => stoppedPath
        (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
      ∀ᵐ ω ∂P, p ≤ P[fun ω => A.indicator (fun _ => (1 : ℝ)) (W ω) |
        MeasurableSpace.comap (fun ω => (O (W ω), Yobs ω)) inferInstance] ω) :
    P.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ (ηL ω) '' Icc
      (MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0 ≤ t ∧
        ηL ω t ∉ ball 0 R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  have hm : Measurable (fun ω => firstHitNonnegativeCurve (ηL ω) 0) := by
    change Measurable ((fun q : C(ℝ, ℂ) × ℂ => firstHitNonnegativeCurve q.1 q.2) ∘
      (fun ω : Ω => (ηL ω, (0 : ℂ))))
    exact measurable_firstHitNonnegativeCurve.comp
      (hC.measurable_curves.1.prodMk measurable_const)
  apply measureReal_firstHit_failure_le_of_matingOfTrees_reference hC R C ε ηsize
    hR hCpos hε hηC hp0 hp1
  intro q hq hq1
  exact condExp_unit_exit_segment_of_augmented_observation P _ hm Yobs hY q ηsize p
    (href q hq hq1)

end LatticeProb

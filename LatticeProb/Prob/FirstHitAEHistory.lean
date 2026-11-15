import LatticeProb.Prob.FirstHitGeneralHistory
import LatticeProb.Prob.CompletedHistoryCondExp
import LatticeProb.LQG.FirstHitForwardExitObservation

/-! # First-hit bounds with almost surely containing histories -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A first-hit failure estimate from an explicit conditional bound given an
ambient history containing the stopped observation up to null events. -/
theorem measureReal_firstHit_failure_le_of_ae_history
    {γ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    {H : MeasurableSpace Ω} (hH : H ≤ mΩ)
    (hO : let W := fun ω => firstHitNonnegativeCurve (ηL ω) 0
      AELeSigma (MeasurableSpace.comap (fun ω => stoppedPath
        (openExitTime (fun t (_ : Unit) => W ω t) (ball 0 1) ()) (W ω))
        inferInstance) H P)
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
  let W := fun ω => firstHitNonnegativeCurve (ηL ω) 0
  let O := fun ω => stoppedPath
    (openExitTime (fun t (_ : Unit) => W ω t) (ball 0 1) ()) (W ω)
  let G := MeasurableSpace.comap O inferInstance
  let : MeasurableSpace Ω := mΩ
  have hW : Measurable W := by
    change Measurable ((fun q : C(ℝ, ℂ) × ℂ => firstHitNonnegativeCurve q.1 q.2) ∘
      (fun ω : Ω => (ηL ω, (0 : ℂ))))
    exact measurable_firstHitNonnegativeCurve.comp
      (hC.measurable_curves.1.prodMk measurable_const)
  have hG : G ≤ mΩ :=
    ((measurable_stoppedPath_openExitTime measurable_id isOpen_ball).comp hW).comap_le
  have hjoin : AELeSigma (H ⊔ G) H P :=
    AELeSigma.sup (AELeSigma.of_le le_rfl) hO
  apply measureReal_firstHit_failure_le_of_history hC (H := H ⊔ G)
    (sup_le hH hG) le_sup_right R C ε ηsize hR hCpos hε hηC hp0 hp1
  intro q hq hq1
  let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
    ∃ y, ball y (ηsize * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
      (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
  have hA : MeasurableSet A :=
    measurableSet_real_exit_segment_contains_ball measurable_id _ _ isOpen_ball isOpen_ball _
  have hf : Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) (W ω)) P :=
    ((integrable_const (1 : ℝ)).indicator hA).comp_measurable hW
  have heq := condExp_ae_eq_of_aeLeSigma (μ := P)
    (le_sup_left : H ≤ H ⊔ G) (sup_le hH hG) hjoin hf
  filter_upwards [href q hq hq1, heq] with ω hpω heqω
  exact heqω ▸ hpω

/-- If a history contains the complex forward stopped path, it contains the
Euclidean first-hit stopped path up to null events. -/
theorem aeLeSigma_firstHit_of_forward_history
    {γ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm) {H : MeasurableSpace Ω} (r : ℝ)
    (hF : MeasurableSpace.comap (fun ω =>
      let w : C(ℝ≥0, ℂ) := (ηL ω).comp ⟨fun t => (t : ℝ), NNReal.continuous_coe⟩
      stoppedPath (openExitTime (fun t (_ : Unit) => w t) (ball 0 r) ()) w)
      inferInstance ≤ H) :
    AELeSigma (MeasurableSpace.comap (fun ω =>
      let v := firstHitNonnegativeCurve (ηL ω) 0
      stoppedPath (openExitTime (fun t (_ : Unit) => v t) (ball 0 r) ()) v)
      inferInstance) H P := by
  let : MeasurableSpace Ω := mΩ
  intro A hA
  obtain ⟨B, hB, hAB⟩ := (aeLeSigma_firstHit_forward_exit_observations hC r).1 A hA
  exact ⟨B, hF B hB, hAB⟩

end LatticeProb

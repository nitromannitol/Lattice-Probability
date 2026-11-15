import LatticeProb.Prob.FirstHitForwardAreaTime
import LatticeProb.Prob.ReferenceLawSpacedExitTrial
import LatticeProb.Prob.FirstHitSpacedBound

/-! # Reference exit estimates for first-hit paths -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A conditional unit-exit estimate for the origin first-hit path law bounds
failure of the corresponding complex trace to contain a ball. -/
theorem measureReal_firstHit_failure_le_of_matingOfTrees_reference
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    (R C ε ηsize : ℝ) (hR : 0 < R) (hCpos : 0 < C) (hε : 0 < ε)
    (hηC : 2 ≤ ηsize * C) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (href : ∀ q : ℝ, 0 < q → q < 1 →
      let ν := P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
        ∃ y, ball y (ηsize * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => stoppedPath
        (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
      ∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap O inferInstance] w) :
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
  have hproper : ∀ᵐ ω ∂P, Tendsto (ηL ω) (cocompact ℝ) (cocompact ℂ) := by
    filter_upwards [hC.spaceFilling] with ω hω
    exact hω.2.1
  apply measureReal_firstHit_failure_le_of_restricted P ηL 0 hproper R (ε * R)
  apply measureReal_real_ballExitTrace_failure_le_of_reference_law P
    (fun ω => firstHitNonnegativeCurve (ηL ω) 0) hm
    (P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)) 0 R C ε ηsize
    hR hCpos hε hηC hp0 hp1
  · exact ae_firstHitNonnegativeCurve_start_of_matingOfTrees hC
  · exact ae_firstHitNonnegativeCurve_exit_of_matingOfTrees hC R
  · intro k hk
    exact map_firstHitNonnegativeCurve_normalize_of_matingOfTrees hC _ _
  · exact href

end LatticeProb

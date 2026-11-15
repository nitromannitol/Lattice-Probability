import LatticeProb.Prob.FirstHitSpacedBound
import LatticeProb.Prob.RealSpacedBallExitTrial

/-! # Conditional exit trials for first-hit traces -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- Conditional success under the canonical first-hit path law bounds the
probability that the original first-hit trace contains no ball. -/
theorem measureReal_firstHit_failure_le_spaced
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : Ω → C(ℝ, ℂ)) (hc : Measurable c) (z : ℂ)
    (hproper : ∀ᵐ ω ∂P, Tendsto (c ω) (cocompact ℝ) (cocompact ℂ))
    (R C ε : ℝ) (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let Φ := fun ω => firstHitNonnegativeCurve (c ω) z
    let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) → EuclideanSpace ℝ (Fin 2) :=
      fun t w => w t
    let hm : ∀ t, StronglyMeasurable (X t) :=
      fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable
    let hcont : ∀ w, Continuous fun t => X t w := fun w => w.continuous
    (∀ᵐ w ∂(P.map Φ), openExitTime X (ball 0 R) w ≠ ⊤) →
    (∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ w ∂(P.map Φ),
      p ≤ (P.map Φ)[({w | ∃ y, ball y (ε * R) ⊆ (fun t : ℝ => X t.toNNReal w) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal w ∉
          ball 0 (((k + 1 : ℕ) : ℝ) * (C * ε * R))})
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal w ∉
          ball 0 (((k + 1 + 1 : ℕ) : ℝ) * (C * ε * R))})}).indicator
          (fun _ => (1 : ℝ)) | ballExitHistory X hm hcont 0
            (fun j => ((j + 1 : ℕ) : ℝ) * (C * ε * R))
            (monotone_spaced_ball_radius hC hε hR) k] w) →
    P.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ (c ω) '' Icc
      (MatedCRTHarmonic.GMS4b.hitTime (c ω) z)
      (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (c ω) z ≤ t ∧
        c ω t ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  dsimp only
  intro hfin hp
  apply measureReal_firstHit_failure_le_of_map P c hc z hproper R (ε * R)
  exact measureReal_real_ballExitTrace_failure_le_spaced
    (fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable)
    (fun w => w.continuous) 0 R C ε hR hC hε hfin hp0 hp1 hp

end LatticeProb

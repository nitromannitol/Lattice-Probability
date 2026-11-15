import LatticeProb.Prob.FirstHitReferenceExitBound

/-! # Uniform exponential constants for first-hit traces -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

/-- A fixed conditional unit-exit estimate gives uniform positive constants
for the exponential first-hit trace bound. -/
theorem exists_firstHit_exponential_bound_of_reference
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}
    (hC : MatedCRTHarmonic.MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀
      B B' B₀ B₀' U ηL η η₀ bm)
    {δ p : ℝ} (hδ : 0 < δ) (hp : 0 < p) (hp1 : p ≤ 1)
    (href : ∀ q : ℝ, 0 < q → q < 1 →
      let ν := P.map (fun ω => firstHitNonnegativeCurve (ηL ω) 0)
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) |
        ∃ y, ball y (δ * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin 2)) => stoppedPath
        (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
      ∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap O inferInstance] w) :
    ∃ a₀ a₁ : ℝ, 0 < a₀ ∧ 0 < a₁ ∧
      ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
        P {ω | ¬ ∃ w, ball w (ε * R) ⊆ (ηL ω) '' Icc
          (MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0)
          (sInf {t : ℝ | MatedCRTHarmonic.GMS4b.hitTime (ηL ω) 0 ≤ t ∧
            ηL ω t ∉ ball 0 R})} ≤ ENNReal.ofReal (a₀ * Real.exp (-a₁ / ε)) := by
  let C : ℝ := 2 / δ
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hδC : 2 ≤ δ * C := by
    simpa only [C, mul_div_cancel₀ 2 (ne_of_gt hδ)] using (le_refl (2 : ℝ))
  refine ⟨Real.exp (p ^ 2), p ^ 2 / (2 * C), Real.exp_pos _, ?_, ?_⟩
  · positivity
  · intro R hR ε hε
    have h := measureReal_firstHit_failure_le_of_matingOfTrees_reference hC R C ε δ
      hR hCpos hε hδC hp.le hp1 href
    have hpow : -(p ^ 2 / 2) * (C * ε)⁻¹ = -(p ^ 2 / (2 * C)) / ε := by
      field_simp
    rw [hpow] at h
    have hm := ENNReal.ofReal_le_ofReal h
    rw [ofReal_measureReal (measure_ne_top P _)] at hm
    exact hm

end LatticeProb

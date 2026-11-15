import LatticeProb.Prob.RealSpacedBallExitTrial

/-! # Spaced exit trials under canonical path laws -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- A spaced-trial estimate on the canonical path law bounds the failure
probability of any measurable realization of that law. -/
theorem measureReal_real_ballExitTrace_failure_le_spaced_of_map
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Φ : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hΦ : Measurable Φ)
    (z : EuclideanSpace ℝ (Fin d)) (R C ε : ℝ)
    (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
      fun t w => w t
    let hm : ∀ t, StronglyMeasurable (X t) :=
      fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable
    let hc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
    (∀ᵐ w ∂(P.map Φ), openExitTime X (ball z R) w ≠ ⊤) →
    (∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ w ∂(P.map Φ),
      p ≤ (P.map Φ)[({w | ∃ y, ball y (ε * R) ⊆ (fun t : ℝ => X t.toNNReal w) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal w ∉
          ball z (((k + 1 : ℕ) : ℝ) * (C * ε * R))})
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal w ∉
          ball z (((k + 1 + 1 : ℕ) : ℝ) * (C * ε * R))})}).indicator
          (fun _ => (1 : ℝ)) | ballExitHistory X hm hc z
            (fun j => ((j + 1 : ℕ) : ℝ) * (C * ε * R))
            (monotone_spaced_ball_radius hC hε hR) k] w) →
    P.real {ω | ¬ ∃ y, ball y (ε * R) ⊆ (fun t : ℝ => Φ ω t.toNNReal) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ Φ ω t.toNNReal ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  dsimp only
  intro hfin hp
  let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun t w => w t
  let hm : ∀ t, StronglyMeasurable (X t) :=
    fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable
  let hc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
  have hb := measureReal_real_ballExitTrace_failure_le_spaced hm hc z R C ε
    hR hC hε hfin hp0 hp1 hp
  calc
    _ ≤ (P.map Φ).real {w | ¬ ∃ y, ball y (ε * R) ⊆
        (fun t : ℝ => X t.toNNReal w) '' Icc 0
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal w ∉ ball z R})} := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      exact Measure.le_map_apply (μ := P) hΦ.aemeasurable
        {w | ¬ ∃ y, ball y (ε * R) ⊆ (fun t : ℝ => X t.toNNReal w) '' Icc 0
          (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal w ∉ ball z R})}
    _ ≤ _ := hb

end LatticeProb

import LatticeProb.Prob.UnitNormalizedSpacedExitTrial

/-! # Unit-normalized exit trials under canonical path laws -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Unit-normalized estimates on a canonical path law bound the failure
probability of any measurable realization of that law. -/
theorem measureReal_real_ballExitTrace_failure_le_of_unit_normalized_map
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Φ : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hΦ : Measurable Φ)
    (z : EuclideanSpace ℝ (Fin d)) (R C ε η : ℝ)
    (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε) (hηC : 2 ≤ η * C)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
      fun t w => w t
    let hc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
    (∀ᵐ w ∂(P.map Φ), X 0 w = z) →
    (∀ᵐ w ∂(P.map Φ), openExitTime X (ball z R) w ≠ ⊤) →
    (∀ k < ⌊(C * ε)⁻¹⌋₊ - 1,
      let s : ℝ≥0 := ⟨((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2, by positivity⟩
      let hs : 0 < s := by
        have ht : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2 := by positivity
        exact_mod_cast ht
      let q := (C * ε * R) / (2 * (s : ℝ))
      let w := pathMap X hc
      let v := fun ω => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp (w ω)).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩
      let B := {ω | ∃ y, ball y (η * q) ⊆ (fun t : ℝ => v ω t.toNNReal) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 1})
        (sInf {t : ℝ | 0 ≤ t ∧ v ω t.toNNReal ∉ ball 0 (1 + q)})}
      let Y := fun ω => stoppedPath
        (openExitTime (fun t (_ : Unit) => ballNormalize z s hs (w ω (areaTimeScale s hs t)))
          (ball 0 1) ()) (v ω)
      ∀ᵐ ω ∂(P.map Φ), p ≤ (P.map Φ)[B.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap Y inferInstance] ω) →
    P.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ (fun t : ℝ => Φ ω t.toNNReal) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ Φ ω t.toNNReal ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  dsimp only
  intro hstart hfin hp
  let X : ℝ≥0 → C(ℝ≥0, EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d) :=
    fun t w => w t
  let hm : ∀ t, StronglyMeasurable (X t) :=
    fun t => (ContinuousMapBorel.ContinuousMap.measurable_eval t).stronglyMeasurable
  let hc : ∀ w, Continuous fun t => X t w := fun w => w.continuous
  have hb := measureReal_real_ballExitTrace_failure_le_of_unit_normalized hm hc z R C ε η
    hR hC hε hηC hstart hfin hp0 hp1 hp
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

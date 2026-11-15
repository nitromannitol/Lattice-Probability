import LatticeProb.Prob.CanonicalUnitNormalizedSpacedExitTrial
import LatticeProb.Prob.NormalizedExitReferenceLaw

/-! # Spaced exit trials under a reference path law -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Reference-law exit estimates imply a failure bound when every trial has
that law after deterministic spatial and temporal normalization. -/
theorem measureReal_real_ballExitTrace_failure_le_of_reference_law
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Φ : Ω → C(ℝ≥0, EuclideanSpace ℝ (Fin d))) (hΦ : Measurable Φ)
    (ν : Measure (C(ℝ≥0, EuclideanSpace ℝ (Fin d))))
    (z : EuclideanSpace ℝ (Fin d)) (R C ε η : ℝ)
    (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε) (hηC : 2 ≤ η * C)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∀ᵐ w ∂(P.map Φ), w 0 = z) →
    (∀ᵐ w ∂(P.map Φ), openExitTime (fun t w => w t) (ball z R) w ≠ ⊤) →
    (∀ k < ⌊(C * ε)⁻¹⌋₊ - 1,
      let s : ℝ≥0 := ⟨((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2, by positivity⟩
      let hs : 0 < s := by
        have ht : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2 := by positivity
        exact_mod_cast ht
      (P.map Φ).map (fun w => ((⟨ballNormalize z s hs, (ballNormalize z s hs).continuous⟩ :
        C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d))).comp w).comp
          ⟨areaTimeScale s hs, (areaTimeScale s hs).continuous⟩) = ν) →
    (∀ q : ℝ, 0 < q → q < 1 →
      let A := {w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) |
        ∃ y, ball y (η * q) ⊆ (fun t : ℝ => w t.toNNReal) '' Icc
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 1})
          (sInf {t : ℝ | 0 ≤ t ∧ w t.toNNReal ∉ ball 0 (1 + q)})}
      let O := fun w : C(ℝ≥0, EuclideanSpace ℝ (Fin d)) => stoppedPath
        (openExitTime (fun t (_ : Unit) => w t) (ball 0 1) ()) w
      ∀ᵐ w ∂ν, p ≤ ν[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap O inferInstance] w) →
    P.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ (fun t : ℝ => Φ ω t.toNNReal) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ Φ ω t.toNNReal ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  intro hstart hfin hlaw href
  apply measureReal_real_ballExitTrace_failure_le_of_unit_normalized_map P Φ hΦ z R C ε η
    hR hC hε hηC hp0 hp1 hstart hfin
  intro k hk
  dsimp only
  let s : ℝ≥0 := ⟨((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2, by positivity⟩
  have hs : 0 < s := by
    have ht : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2 := by positivity
    exact_mod_cast ht
  let q : ℝ := (C * ε * R) / (2 * (s : ℝ))
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_one (by positivity)).2
    change C * ε * R < 2 * (((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2)
    have ha : 0 < ((k + 1 : ℕ) : ℝ) * (C * ε * R) := by positivity
    linarith
  have ht := condExp_unit_exit_segment_of_normalized_path_law (P.map Φ) ν z s hs q η p
    (hlaw k hk) (href q hq0 hq1)
  exact ht

end LatticeProb

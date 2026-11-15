import LatticeProb.Topology.NestedExitTrial
import LatticeProb.Prob.FlooredTrialRate

/-! # Inverse-scale bounds for nested exit traces -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- A floored number of conditionally successful nested exit trials gives an
inverse-scale exponential bound for failure of the outer trace to contain a ball. -/
theorem measureReal_firstExitTrace_failure_le_floor_inv
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (ℱ : Filtration ℕ m) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (R a C ε : ℝ)
    (hr : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, r k ≤ R ∧ r (k + 1) ≤ R)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      openExitTime (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ))) (ball z R) () ≠ ⊤)
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] {ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})})
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k, ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})}).indicator
        (fun _ => (1 : ℝ)) | ℱ k] ω) :
    μ.real {ω | ¬ ∃ w, ball w a ⊆ η ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  calc
    _ ≤ Real.exp (-(p ^ 2 / 2) * ((⌊(C * ε)⁻¹⌋₊ - 1 : ℕ) : ℝ)) :=
      measureReal_firstExitTrace_failure_le_of_condExp_ge ℱ η t₀ z r R a _
        hr hpath hA hp0 hp1 hp
    _ ≤ Real.exp (2 * (p ^ 2 / 2)) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) :=
      exp_neg_mul_floor_sub_one_le _ _ (by positivity)
    _ = _ := by congr 1; ring

end LatticeProb

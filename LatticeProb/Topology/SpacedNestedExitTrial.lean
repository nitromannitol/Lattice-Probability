import LatticeProb.Topology.FiniteNestedExitTrial

/-! # Equally spaced nested exit trials -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- The first `⌊(C * ε)⁻¹⌋₊` positive multiples of `C * ε * R`
are at most `R`. -/
theorem spaced_radius_le {C ε R : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hR : 0 < R) {j : ℕ} (hj : j ≤ ⌊(C * ε)⁻¹⌋₊) :
    (j : ℝ) * (C * ε * R) ≤ R := by
  have hc : 0 < C * ε := mul_pos hC hε
  have hj' : (j : ℝ) ≤ (C * ε)⁻¹ :=
    (Nat.cast_le.mpr hj).trans (Nat.floor_le (inv_nonneg.mpr hc.le))
  have hm : (j : ℝ) * (C * ε) ≤ 1 := by
    calc
      (j : ℝ) * (C * ε) ≤ (C * ε)⁻¹ * (C * ε) :=
        mul_le_mul_of_nonneg_right hj' hc.le
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hc)
  nlinarith

/-- A finite collection of equally spaced exit trials gives an inverse-scale
bound when each trial satisfies the stated conditional success estimate. -/
theorem measureReal_firstExitTrace_failure_le_of_spaced_condExp
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (ℱ : Filtration ℕ m) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (R C ε : ℝ) (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      openExitTime (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ))) (ball z R) () ≠ ⊤)
    (hA : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, MeasurableSet[ℱ (k + 1)]
      {ω | ∃ w, ball w (ε * R) ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 1 : ℕ) * (C * ε * R))})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 2 : ℕ) * (C * ε * R))})})
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ ω ∂μ,
      p ≤ μ[({ω | ∃ w, ball w (ε * R) ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 1 : ℕ) * (C * ε * R))})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 2 : ℕ) * (C * ε * R))})}).indicator
        (fun _ => (1 : ℝ)) | ℱ k] ω) :
    μ.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ η ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  apply measureReal_firstExitTrace_failure_le_floor_inv_on_range ℱ η t₀ z
    (fun k => ((k + 1 : ℕ) : ℝ) * (C * ε * R)) R (ε * R) C ε
  · intro k hk
    constructor
    · apply spaced_radius_le hC hε hR
      omega
    · apply spaced_radius_le hC hε hR
      omega
  · exact hpath
  · simpa only [Nat.add_assoc] using hA
  · exact hp0
  · exact hp1
  · simpa only [Nat.add_assoc] using hp

end LatticeProb

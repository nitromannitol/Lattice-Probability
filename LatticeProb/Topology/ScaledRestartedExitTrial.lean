import LatticeProb.Topology.RestartedNestedExitBall

/-! # Scaled restarted exit trials -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Conditional success for restarted half-width traces yields an exponential
bound for failure of the full exit trace to contain a ball. -/
theorem measureReal_firstExitTrace_failure_le_of_restarted_condExp
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (ℱ : Filtration ℕ m) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (R C ε δ : ℝ)
    (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε) (hδC : 2 ≤ δ * C)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      openExitTime (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ))) (ball z R) () ≠ ⊤)
    (hA : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, MeasurableSet[ℱ (k + 1)]
      {ω | ∃ w, ball w (ε * R) ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 1 : ℕ) * (C * ε * R))})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 2 : ℕ) * (C * ε * R))})})
    (hS : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, MeasurableSet[m]
      {ω | ∃ w, ball w (δ * (C * ε * R) / 2) ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 1 : ℕ) * (C * ε * R))})
      (sInf {t : ℝ | sInf {u : ℝ | t₀ ω ≤ u ∧ η ω u ∉
        ball z ((k + 1 : ℕ) * (C * ε * R))} ≤ t ∧ η ω t ∉
        ball z (((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2)})})
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ ω ∂μ,
      p ≤ μ[({ω | ∃ w, ball w (δ * (C * ε * R) / 2) ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z ((k + 1 : ℕ) * (C * ε * R))})
      (sInf {t : ℝ | sInf {u : ℝ | t₀ ω ≤ u ∧ η ω u ∉
        ball z ((k + 1 : ℕ) * (C * ε * R))} ≤ t ∧ η ω t ∉
        ball z (((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2)})}).indicator
        (fun _ => (1 : ℝ)) | ℱ k] ω) :
    μ.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ η ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  apply measureReal_firstExitTrace_failure_le_of_spaced_condExp ℱ η t₀ z R C ε hR hC hε hpath hA hp0 hp1
  intro k hk
  have hd : 0 < C * ε * R := mul_pos (mul_pos hC hε) hR
  have hout : ((k + 2 : ℕ) : ℝ) * (C * ε * R) ≤ R := by
    apply spaced_radius_le hC hε hR
    omega
  have hrs : ((k + 1 : ℕ) : ℝ) * (C * ε * R) ≤
      ((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2 := by linarith
  have hsR : ((k + 1 : ℕ) : ℝ) * (C * ε * R) + (C * ε * R) / 2 ≤
      ((k + 2 : ℕ) : ℝ) * (C * ε * R) := by
    push_cast
    nlinarith
  have hfin : ∀ᵐ ω ∂μ, openExitTime
      (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ)))
      (ball z (((k + 2 : ℕ) : ℝ) * (C * ε * R))) () ≠ ⊤ := by
    filter_upwards [hpath] with ω hω
    exact ne_top_of_le_ne_top hω.2 (monotone_openExitTime_ball _ () z hout)
  exact condExp_restarted_nested_exit_ball (ℱ k) η t₀ (fun _ => z) hrs hsR
    (target_radius_le_half_width hε.le hR.le hδC) (hpath.mono fun _ h => h.1)
    hfin (hS k hk) ((ℱ.le (k + 1)) _ (hA k hk)) (hp k hk)

end LatticeProb

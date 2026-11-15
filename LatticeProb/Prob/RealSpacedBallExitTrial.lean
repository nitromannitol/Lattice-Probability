import LatticeProb.Prob.RealBallExitTrial
import LatticeProb.Topology.SpacedNestedExitTrial

/-! # Equally spaced trials at real-time ball exits -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Positive equally spaced radii form a monotone sequence. -/
theorem monotone_spaced_ball_radius {C ε R : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hR : 0 < R) : Monotone (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * (C * ε * R)) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_right _ (le_of_lt (mul_pos (mul_pos hC hε) hR))
  exact_mod_cast Nat.add_le_add_right hij 1

/-- Conditional success for actual exit segments gives an inverse-scale bound
for the full real-time trace, using the natural stopped ball-exit history. -/
theorem measureReal_real_ballExitTrace_failure_le_spaced
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) (R C ε : ℝ)
    (hR : 0 < R) (hC : 0 < C) (hε : 0 < ε)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ ω ∂μ,
      p ≤ μ[({ω | ∃ w, ball w (ε * R) ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉
          ball z (((k + 1 : ℕ) : ℝ) * (C * ε * R))})
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉
          ball z (((k + 1 + 1 : ℕ) : ℝ) * (C * ε * R))})}).indicator
          (fun _ => (1 : ℝ)) | ballExitHistory X hm hc z
            (fun j => ((j + 1 : ℕ) : ℝ) * (C * ε * R))
            (monotone_spaced_ball_radius hC hε hR) k] ω) :
    μ.real {ω | ¬ ∃ w, ball w (ε * R) ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  calc
    _ ≤ Real.exp (-(p ^ 2 / 2) * ((⌊(C * ε)⁻¹⌋₊ - 1 : ℕ) : ℝ)) := by
      apply measureReal_real_ballExitTrace_failure_le hm hc z
        (fun j => ((j + 1 : ℕ) : ℝ) * (C * ε * R))
        (monotone_spaced_ball_radius hC hε hR) R (ε * R)
        (⌊(C * ε)⁻¹⌋₊ - 1) (mul_pos hε hR)
      · intro k hk
        constructor
        · apply spaced_radius_le hC hε hR
          omega
        · apply spaced_radius_le hC hε hR
          omega
      · exact hfin
      · exact hp0
      · exact hp1
      · exact hp
    _ ≤ Real.exp (2 * (p ^ 2 / 2)) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) :=
      exp_neg_mul_floor_sub_one_le _ _ (by positivity)
    _ = _ := by congr 1; ring

end LatticeProb

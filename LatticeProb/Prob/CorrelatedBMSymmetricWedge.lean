import LatticeProb.Prob.CorrelatedBMWhitening
import LatticeProb.Prob.CorrelatedBMJointWindowTransfer

/-! # Symmetric wedge representation of a joint Brownian barrier -/

set_option autoImplicit false

open MeasureTheory Set
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- A symmetric wedge barrier for the increments of a continuous planar path. -/
def symmetricWedgeBarrier (a b q h : ℝ) : Set Path2 :=
  {ω | ∀ t ∈ Icc 0 h,
    |b * coneIncr 1 t 0 ω| ≤ q + a * coneIncr 0 t 0 ω}

/-- The symmetric wedge barrier is closed in the compact-open topology. -/
theorem isClosed_symmetricWedgeBarrier (a b q h : ℝ) :
    IsClosed (symmetricWedgeBarrier a b q h) := by
  have heq : symmetricWedgeBarrier a b q h =
      ⋂ t : ℝ, ⋂ _ : t ∈ Icc (0 : ℝ) h,
        {ω : Path2 | |b * coneIncr 1 t 0 ω| ≤ q + a * coneIncr 0 t 0 ω} := by
    ext ω
    simp only [symmetricWedgeBarrier, mem_ofPred_eq, mem_iInter]
  rw [heq]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro ht
  apply isClosed_le <;> unfold coneIncr lrCoord <;> split_ifs <;> fun_prop

/-- Sum-difference whitening expresses a joint barrier as a symmetric wedge. -/
theorem mem_symmetricWedgeBarrier_whitenAt_iff (γ q h : ℝ) (ω : Path2)
    (ha : Real.sqrt (2 * (1 + lrCov γ 0 1)) ≠ 0)
    (hb : Real.sqrt (2 * (1 - lrCov γ 0 1)) ≠ 0) :
    whitenAt γ 0 ω ∈ symmetricWedgeBarrier
      (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
      (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2) q h ↔
      ω ∈ jointZeroBarrier q h := by
  have hu (t : ℝ) :
      Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2 *
          coneIncr 0 t 0 (whitenAt γ 0 ω) =
        (coneIncr 0 t 0 ω + coneIncr 1 t 0 ω) / 2 := by
    simp only [coneIncr, lrCoord_zero_whitenAt, zero_add, sub_self, zero_div, sub_zero]
    field_simp
    ring
  have hv (t : ℝ) :
      Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2 *
          coneIncr 1 t 0 (whitenAt γ 0 ω) =
        (coneIncr 0 t 0 ω - coneIncr 1 t 0 ω) / 2 := by
    simp only [coneIncr, lrCoord_one_whitenAt, zero_add, sub_self, zero_div, sub_zero]
    field_simp
    ring
  simp only [symmetricWedgeBarrier, jointZeroBarrier, mem_ofPred_eq, mem_inter_iff, hu, hv, abs_le]
  constructor
  · intro H
    constructor <;> intro t ht <;> have := H t ht <;> linarith
  · rintro ⟨H₀, H₁⟩ t ht
    have h₀ := H₀ t ht
    have h₁ := H₁ t ht
    constructor <;> linarith

/-- Whitening transfers the joint barrier probability to a symmetric wedge. -/
theorem measure_jointZeroBarrier_eq_symmetricWedge {γ : ℝ} {μ : Measure Path2}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (q h : ℝ) :
    μ (jointZeroBarrier q h) =
      (μ.map (whitenAt γ 0)) (symmetricWedgeBarrier
        (Real.sqrt (2 * (1 + lrCov γ 0 1)) / 2)
        (Real.sqrt (2 * (1 - lrCov γ 0 1)) / 2) q h) := by
  have hθ0 : 0 < Real.pi * γ ^ 2 / 4 := by positivity
  have hθπ : Real.pi * γ ^ 2 / 4 < Real.pi := by
    have hγ4 : γ ^ 2 < 4 := by nlinarith [mul_pos hγ0 (sub_pos.2 hγ2)]
    nlinarith [mul_pos Real.pi_pos (sub_pos.2 hγ4)]
  have hc1 : Real.cos (Real.pi * γ ^ 2 / 4) < 1 := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rwa [Real.cos_zero] at hh
  have hcm1 : -1 < Real.cos (Real.pi * γ ^ 2 / 4) := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rwa [Real.cos_pi] at hh
  have hρ : lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := rfl
  have ha : Real.sqrt (2 * (1 + lrCov γ 0 1)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    rw [hρ]
    linarith
  have hb : Real.sqrt (2 * (1 - lrCov γ 0 1)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    rw [hρ]
    linarith
  rw [Measure.map_apply (continuous_whitenAt γ 0).measurable
    (isClosed_symmetricWedgeBarrier _ _ _ _).measurableSet]
  congr 1
  ext ω
  exact (mem_symmetricWedgeBarrier_whitenAt_iff γ q h ω ha hb).symm

end LatticeProb.CorrelatedBM

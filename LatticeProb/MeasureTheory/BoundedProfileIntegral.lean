import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Integral estimates for bounded profiles -/

set_option autoImplicit false

open MeasureTheory

namespace LatticeProb

/-- Bounded nonnegative profiles are controlled by their truncated pointwise discrepancy. -/
theorem abs_sub_le_max_mul_min {a b d L : ℝ}
    (ha : 0 ≤ a ∧ a ≤ L) (hb : 0 ≤ b ∧ b ≤ L) (hd : |a - b| ≤ d) :
    |a - b| ≤ max 1 L * min 1 d := by
  have hL : 0 ≤ L := ha.1.trans ha.2
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have hC : 1 ≤ max 1 L := le_max_left _ _
  have hCL : L ≤ max 1 L := le_max_right _ _
  by_cases h : d ≤ 1
  · rw [min_eq_right h]
    nlinarith
  · rw [min_eq_left (le_of_not_ge h)]
    have hab : |a - b| ≤ L := abs_le.mpr ⟨by linarith [hb.2, ha.1], by linarith [ha.2, hb.1]⟩
    simpa using hab.trans hCL

/-- The difference of integrals over any set is bounded by the integral of the truncated
pointwise discrepancy, multiplied by the common profile bound. -/
theorem abs_setIntegral_sub_le_truncated_discrepancy
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g d : X → ℝ} {L : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hd : Integrable (fun x => min 1 (d x)) μ)
    (h : ∀ᵐ x ∂μ, (0 ≤ f x ∧ f x ≤ L) ∧ (0 ≤ g x ∧ g x ≤ L) ∧
      |f x - g x| ≤ d x) (s : Set X) :
    |∫ x in s, f x ∂μ - ∫ x in s, g x ∂μ| ≤
      max 1 L * ∫ x in s, min 1 (d x) ∂μ := by
  have hf' := hf.mono_measure (Measure.restrict_le_self : μ.restrict s ≤ μ)
  have hg' := hg.mono_measure (Measure.restrict_le_self : μ.restrict s ≤ μ)
  have hd' := hd.mono_measure (Measure.restrict_le_self : μ.restrict s ≤ μ)
  calc
    |∫ x in s, f x ∂μ - ∫ x in s, g x ∂μ| =
        |∫ x in s, (f x - g x) ∂μ| := by rw [integral_sub hf' hg']
    _ ≤ ∫ x in s, |f x - g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x in s, max 1 L * min 1 (d x) ∂μ := by
      apply integral_mono_ae (hf'.sub hg').abs (hd'.const_mul _)
      filter_upwards [ae_restrict_of_ae h] with x hx
      exact abs_sub_le_max_mul_min hx.1 hx.2.1 hx.2.2
    _ = max 1 L * ∫ x in s, min 1 (d x) ∂μ := integral_const_mul _ _

end LatticeProb

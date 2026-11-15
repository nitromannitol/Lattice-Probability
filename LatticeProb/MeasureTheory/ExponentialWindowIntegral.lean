import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exponentially weighted integrals on finite windows -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- A nonnegative integral on a finite time window is controlled by the
exponentially weighted integral on the same window. -/
theorem integral_Ioo_le_exp_mul_integral_exp_neg_mul
    (T : ℝ) (g : ℝ → ℝ)
    (hg : Integrable g (volume.restrict (Ioo 0 T)))
    (hw : Integrable (fun t => Real.exp (-t) * g t) (volume.restrict (Ioo 0 T)))
    (hpos : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), 0 ≤ g t) :
    ∫ t in Ioo 0 T, g t ≤
      Real.exp T * ∫ t in Ioo 0 T, Real.exp (-t) * g t := by
  rw [← integral_const_mul]
  apply integral_mono_ae hg (hw.const_mul (Real.exp T))
  filter_upwards [hpos, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  have he : (1 : ℝ) ≤ Real.exp T * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith [hmem.2])
  nlinarith

/-- The same window integral is bounded by the weighted integral on the
positive half-line. -/
theorem integral_Ioo_le_exp_mul_integral_Ioi_exp_neg_mul
    (T : ℝ) (g : ℝ → ℝ)
    (hg : Integrable g (volume.restrict (Ioo 0 T)))
    (hw : Integrable (fun t => Real.exp (-t) * g t) (volume.restrict (Ioi 0)))
    (hpos : ∀ᵐ t ∂(volume.restrict (Ioi 0)), 0 ≤ g t) :
    ∫ t in Ioo 0 T, g t ≤
      Real.exp T * ∫ t in Ioi 0, Real.exp (-t) * g t := by
  have hle : volume.restrict (Ioo 0 T) ≤ volume.restrict (Ioi 0) :=
    Measure.restrict_mono_set volume Ioo_subset_Ioi_self
  calc
    _ ≤ Real.exp T * ∫ t in Ioo 0 T, Real.exp (-t) * g t :=
      integral_Ioo_le_exp_mul_integral_exp_neg_mul T g hg
        (hw.mono_measure hle) (ae_mono hle hpos)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_mono_measure hle
        (hpos.mono fun t ht => mul_nonneg (Real.exp_pos _).le ht) hw)
      (Real.exp_pos T).le

end LatticeProb

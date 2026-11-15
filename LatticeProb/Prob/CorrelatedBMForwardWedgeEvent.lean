import LatticeProb.Prob.CorrelatedBMForwardSpace
import LatticeProb.Prob.CorrelatedBMWedgeExit

/-! # Forward Brownian paths and symmetric wedge barriers -/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- Starting point for the normalized forward path along the wedge axis. -/
noncomputable def normalizedWedgeStart (a q : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![q / (a * Real.sqrt 2), 0]

/-- The strict barrier equals wedge survival for a path starting at zero. -/
theorem mem_openSymmetricWedgeBarrier_iff_normalized_forward
    (a b q : ℝ) (ha : a ≠ 0) (T : ℝ≥0) (ω : Path2)
    (hzero : ∀ i : Fin 2, lrCoord i 0 ω = 0) :
    ω ∈ openSymmetricWedgeBarrier a b q T ↔
      ∀ t ≤ T,
        let z := Complex.orthonormalBasisOneI.repr.symm
          (normalizedWedgeStart a q + normalizedForwardSpace t ω)
        (z.re, z.im) ∈ openSymmetricWedge a b := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hpoint (t : ℝ≥0) :
      (let z := Complex.orthonormalBasisOneI.repr.symm
          (normalizedWedgeStart a q + normalizedForwardSpace t ω);
        (z.re, z.im) ∈ openSymmetricWedge a b) ↔
        |b * coneIncr 1 t 0 ω| < q + a * coneIncr 0 t 0 ω := by
    simp only [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      zero_add, add_zero, openSymmetricWedge, mem_ofPred_eq, PiLp.add_apply,
      normalizedWedgeStart, normalizedForwardSpace,
      Matrix.cons_val_zero, Matrix.cons_val_one, halfPath,
      halfTime_true, coneIncr, hzero, sub_zero]
    rw [show q / (a * Real.sqrt 2) + lrCoord 0 ↑t ω / Real.sqrt 2 =
      (q / a + lrCoord 0 ↑t ω) / Real.sqrt 2 by field_simp]
    rw [← mul_div_assoc, abs_div, abs_of_pos hs, ← mul_div_assoc,
      div_lt_div_iff_of_pos_right hs]
    have : a * (q / a + lrCoord 0 ↑t ω) = q + a * lrCoord 0 ↑t ω := by field_simp
    rw [this]
  constructor
  · intro h t ht
    exact (hpoint t).2 (h t ⟨t.coe_nonneg, by exact_mod_cast ht⟩)
  · intro h t ht
    let s : ℝ≥0 := ⟨t, ht.1⟩
    exact (hpoint s).1 (h s (by exact_mod_cast ht.2))

end LatticeProb.CorrelatedBM

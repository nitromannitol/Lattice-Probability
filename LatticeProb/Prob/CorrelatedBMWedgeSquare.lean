import LatticeProb.Prob.CorrelatedBMWedgeKilledHeat
import LatticeProb.Prob.KilledHeatTranslation

/-! # A square inside a symmetric wedge -/

set_option autoImplicit false

open Set
open scoped NNReal
open LQGMetric.HeatSq LQGMetric.KilledHeat

namespace LatticeProb.CorrelatedBM

/-- A positive square centered at the starting point lies inside the strict wedge. -/
theorem translated_sqOpen_subset_complexSymmetricWedge {a b q : ℝ}
    (ha : 0 < a) (hq : 0 < q) :
    let r := q / (2 * (a + |b| + 1))
    0 < r ∧
      {v : ℂ | v - (q / a : ℝ) ∈ sqOpen (-r) (2 * r)} ⊆
        complexSymmetricWedge a b := by
  let r := q / (2 * (a + |b| + 1))
  have hd : 0 < 2 * (a + |b| + 1) := by positivity
  have hr : 0 < r := div_pos hq hd
  have hrbound : (a + |b|) * r < q := by
    have heq : (2 * (a + |b| + 1)) * r = q := by
      dsimp [r]
      field_simp
    have hb : 0 ≤ |b| := abs_nonneg b
    nlinarith
  refine ⟨hr, ?_⟩
  intro v hv
  simp only [sqOpen, mem_ofPred_eq, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hv
  have him : |v.im| < r := abs_lt.mpr ⟨by linarith [hv.2.2.1], by linarith [hv.2.2.2]⟩
  have hab : |b * v.im| ≤ |b| * r := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt him) (abs_nonneg b)
  have hqa : a * (q / a) = q := by field_simp
  change |b * v.im| < a * v.re
  nlinarith [hv.1]

/-- The corresponding square Dirichlet kernel is a local wedge-kernel lower bound. -/
theorem sqDirKernel_le_wedge_killedHeat {a b q : ℝ}
    (ha : 0 < a) (hq : 0 < q) {t : ℝ≥0} (ht : t ≠ 0) (z w : ℂ)
    (hz : z ∈ sqOpen (-(q / (2 * (a + |b| + 1))))
      (2 * (q / (2 * (a + |b| + 1)))))
    (hw : w ∈ sqOpen (-(q / (2 * (a + |b| + 1))))
      (2 * (q / (2 * (a + |b| + 1))))) :
    sqDirKernel (-(q / (2 * (a + |b| + 1))) )
      (2 * (q / (2 * (a + |b| + 1)))) t z w ≤
      killedHeat (complexSymmetricWedge a b) t (z + (q / a : ℝ)) (w + (q / a : ℝ)) := by
  have h := translated_sqOpen_subset_complexSymmetricWedge (b := b) ha hq
  exact sqDirKernel_le_killedHeat_of_translate_subset (by positivity) ht _ _ _ hz hw h.2

end LatticeProb.CorrelatedBM

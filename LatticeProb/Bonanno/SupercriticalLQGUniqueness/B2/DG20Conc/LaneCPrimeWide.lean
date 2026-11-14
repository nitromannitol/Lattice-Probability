/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeWide at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAnnuli

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

def laneCPrimeWideRect : Fin 4 → MarkedRect
  | 0 => ⟨-3 / 16, 17 / 16, 11 / 8, 1 / 8, true⟩
  | 1 => ⟨-3 / 16, -3 / 16, 11 / 8, 1 / 8, true⟩
  | 2 => ⟨-3 / 16, -3 / 16, 1 / 8, 11 / 8, false⟩
  | _ => ⟨17 / 16, -3 / 16, 1 / 8, 11 / 8, false⟩

private theorem laneC_sq_le {a r : ℝ} (h₁ : -r ≤ a) (h₂ : a ≤ r) :
    a ^ 2 ≤ r ^ 2 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ r - a)
    (by linarith : 0 ≤ r + a)]

private theorem laneC_prime_buffered {z w : ℂ}
    (hw : w ∈ laneCUnitBlock) (hz : z ∉ laneCUnitBlock)
    (hre : (z - w).re ^ 2 ≤ (11 / 16 : ℝ) ^ 2)
    (him : (z - w).im ^ 2 ≤ (11 / 16 : ℝ) ^ 2) :
    z ∈ laneCPrimeAround := by
  have hnorm : ‖z - w‖ ^ 2 = (z - w).re ^ 2 + (z - w).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hdist : dist z w < 1 := by
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (z - w)]
  exact ⟨Metric.mem_thickening_iff.mpr ⟨w, hw, hdist⟩, hz⟩

theorem laneC_prime_wide_subset (j : Fin 4) :
    (laneCPrimeWideRect j).toSet ⊆ laneCPrimeAround := by
  fin_cases j <;> intro z hz <;>
    norm_num [laneCPrimeWideRect, MarkedRect.toSet,
      Complex.mem_reProdIm] at hz
  · apply laneC_prime_buffered (w := (⟨1 / 2, 1⟩ : ℂ))
      (by norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm])
      (by intro h; norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm] at h; linarith [hz.2.1])
    · apply laneC_sq_le <;> simp only [Complex.sub_re] <;> linarith [hz.1.1, hz.1.2]
    · apply laneC_sq_le <;> simp only [Complex.sub_im] <;> linarith [hz.2.1, hz.2.2]
  · apply laneC_prime_buffered (w := (⟨1 / 2, 0⟩ : ℂ))
      (by norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm])
      (by intro h; norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm] at h; linarith [hz.2.2])
    · apply laneC_sq_le <;> simp only [Complex.sub_re] <;> linarith [hz.1.1, hz.1.2]
    · apply laneC_sq_le <;> simp only [Complex.sub_im] <;> linarith [hz.2.1, hz.2.2]
  · apply laneC_prime_buffered (w := (⟨0, 1 / 2⟩ : ℂ))
      (by norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm])
      (by intro h; norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm] at h; linarith [hz.1.2])
    · apply laneC_sq_le <;> simp only [Complex.sub_re] <;> linarith [hz.1.1, hz.1.2]
    · apply laneC_sq_le <;> simp only [Complex.sub_im] <;> linarith [hz.2.1, hz.2.2]
  · apply laneC_prime_buffered (w := (⟨1, 1 / 2⟩ : ℂ))
      (by norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm])
      (by intro h; norm_num [laneCUnitBlock, rectAB, MarkedRect.toSet,
        Complex.mem_reProdIm] at h; linarith [hz.1.1])
    · apply laneC_sq_le <;> simp only [Complex.sub_re] <;> linarith [hz.1.1, hz.1.2]
    · apply laneC_sq_le <;> simp only [Complex.sub_im] <;> linarith [hz.2.1, hz.2.2]

end SupercriticalLQGUniqueness.B2.DG20Conc

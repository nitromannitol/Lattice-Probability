/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSourceIdxVisited at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRadius

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneB_dyBlock_diameter_le_two {K : ℕ} {b : ℤ × ℤ}
    {z y : ℂ} (hz : z ∈ T20.dyBlock K b)
    (hy : y ∈ T20.dyBlock K b) :
    dist z y ≤ 2 * (2 : ℝ)⁻¹ ^ K := by
  have hr : 0 ≤ (2 : ℝ)⁻¹ ^ K := by positivity
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc] at hz hy
  rw [dist_eq_norm]
  have hre : |(z - y).re| ≤ (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_re, abs_le]
    constructor <;> nlinarith [hz.1.1, hz.1.2, hy.1.1, hy.1.2]
  have him : |(z - y).im| ≤ (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_im, abs_le]
    constructor <;> nlinarith [hz.2.1, hz.2.2, hy.2.1, hy.2.2]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

end SupercriticalLQGUniqueness.B2.DG20Conc

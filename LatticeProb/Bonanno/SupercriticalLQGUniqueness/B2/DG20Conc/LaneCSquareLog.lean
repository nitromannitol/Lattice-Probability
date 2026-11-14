/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareLog at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPathDegree
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LogCross

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_log_neg_add_pi_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) + (Real.pi : ℂ) * Complex.I = Complex.log z := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.log_re, norm_neg,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · simp only [Complex.add_im, Complex.log_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
    ring

 
theorem laneC_log_neg_add_pi_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) + (Real.pi : ℂ) * Complex.I =
      Complex.log z + (2 * Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
    ring

 
theorem laneC_continuousOn_log_upper {g : ℝ → ℂ} {S : Set ℝ}
    (hg : ContinuousOn g S) (him : ∀ t ∈ S, 0 < (g t).im) :
    ContinuousOn (fun t => Complex.log (g t)) S := by
  exact hg.clog (fun t ht => Complex.mem_slitPlane_iff.mpr
    (Or.inr (ne_of_gt (him t ht))))

 
theorem laneC_continuousOn_log_right {g : ℝ → ℂ} {S : Set ℝ}
    (hg : ContinuousOn g S) (hre : ∀ t ∈ S, 0 < (g t).re) :
    ContinuousOn (fun t => Complex.log (g t)) S := by
  exact hg.clog (fun t ht => Complex.mem_slitPlane_iff.mpr
    (Or.inl (hre t ht)))

end SupercriticalLQGUniqueness.B2.DG20Conc

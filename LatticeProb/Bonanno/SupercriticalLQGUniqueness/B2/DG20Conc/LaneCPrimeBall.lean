/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeBall at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeSep

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

theorem laneC_prime_wide_ball (j : Fin 4) {z : ℂ}
    (hz : z ∈ (laneCPrimeWideRect j).toSet) :
    dist z laneCPrimeCenter < 1 := by
  have hbox : -3 / 16 ≤ z.re ∧ z.re ≤ 19 / 16 ∧
      -3 / 16 ≤ z.im ∧ z.im ≤ 19 / 16 := by
    fin_cases j <;>
      norm_num [laneCPrimeWideRect, MarkedRect.toSet,
        Complex.mem_reProdIm] at hz ⊢ <;>
      rcases hz with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hre : (z - laneCPrimeCenter).re ^ 2 ≤ (11 / 16 : ℝ) ^ 2 := by
    have hlo : -(11 / 16 : ℝ) ≤ (z - laneCPrimeCenter).re := by
      simp only [Complex.sub_re, laneCPrimeCenter]
      linarith [hbox.1]
    have hhi : (z - laneCPrimeCenter).re ≤ (11 / 16 : ℝ) := by
      simp only [Complex.sub_re, laneCPrimeCenter]
      linarith [hbox.2.1]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (11 / 16 : ℝ) - (z - laneCPrimeCenter).re)
      (by linarith : 0 ≤ (11 / 16 : ℝ) + (z - laneCPrimeCenter).re)]
  have him : (z - laneCPrimeCenter).im ^ 2 ≤ (11 / 16 : ℝ) ^ 2 := by
    have hlo : -(11 / 16 : ℝ) ≤ (z - laneCPrimeCenter).im := by
      simp only [Complex.sub_im, laneCPrimeCenter]
      linarith [hbox.2.2.1]
    have hhi : (z - laneCPrimeCenter).im ≤ (11 / 16 : ℝ) := by
      simp only [Complex.sub_im, laneCPrimeCenter]
      linarith [hbox.2.2.2]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (11 / 16 : ℝ) - (z - laneCPrimeCenter).im)
      (by linarith : 0 ≤ (11 / 16 : ℝ) + (z - laneCPrimeCenter).im)]
  have hnorm : ‖z - laneCPrimeCenter‖ ^ 2 =
      (z - laneCPrimeCenter).re ^ 2 + (z - laneCPrimeCenter).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (z - laneCPrimeCenter)]

end SupercriticalLQGUniqueness.B2.DG20Conc

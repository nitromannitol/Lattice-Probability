/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.MedianWindowAdapter at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.Inputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBX0Window

 


set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

 

private lemma eventual_dyadic_constant_bounds
    {a δ c C : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (-(a + δ) * (n : ℝ)) ≤
        c * (2 : ℝ) ^ (-(a + δ / 2) * (n : ℝ)) ∧
      C * (2 : ℝ) ^ (-(a - δ / 2) * (n : ℝ)) ≤
        (2 : ℝ) ^ (-(a - δ) * (n : ℝ)) := by
  have hθ : 0 < (δ / 2) * Real.log 2 :=
    mul_pos (by linarith) (Real.log_pos (by norm_num))
  have ht : Tendsto (fun n : ℕ => ((δ / 2) * Real.log 2) * (n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hθ
  have he := ht.eventually
    (eventually_ge_atTop (max (-Real.log c) (Real.log C)))
  filter_upwards [he] with n hn
  have hc' : -Real.log c ≤ ((δ / 2) * Real.log 2) * (n : ℝ) :=
    (le_max_left _ _).trans hn
  have hC' : Real.log C ≤ ((δ / 2) * Real.log 2) * (n : ℝ) :=
    (le_max_right _ _).trans hn
  constructor
  · rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_log hc, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hc']
  · rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_log hC, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hC']

 
theorem whiteNoiseMedianPowerWindow_proved : Inputs.WhiteNoiseMedianPowerWindow := by
  intro ξ Q hQ Ω _ P W hW δ hδ
  obtain ⟨c, C, hc, hC, hwindow⟩ :=
    DG20Conc.laneB_whiteNoise_median_window ξ Q hQ (δ / 2) (by linarith : 0 < δ / 2)
  have hbounds := eventual_dyadic_constant_bounds
    (a := 1 - (ξ : ℝ) * Q) hδ hc hC
  filter_upwards [hbounds] with n hn
  have hw := hwindow P W hW n
  constructor
  · convert hn.1.trans hw.1 using 1
  · convert hw.2.trans hn.2 using 1

end SupercriticalLQGUniqueness.B2.QPos

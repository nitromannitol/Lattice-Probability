/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedTail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedPolar

 
























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 

 
lemma heatKernel_le_of_ge {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (z w : ℂ) (hw : a ≤ ‖z - w‖) :
    heatKernel s z w ≤ 2 * Real.exp (-(a ^ 2 / (4 * s))) * heatKernel (2 * s) z w := by
  unfold heatKernel
  have ht : a ^ 2 ≤ ‖z - w‖ ^ 2 := pow_le_pow_left₀ ha hw 2
  set t := ‖z - w‖ ^ 2
  have e1 : -t / (2 * s) = -t / (2 * (2 * s)) + -t / (4 * s) := by
    field_simp; ring
  have e2 : -t / (4 * s) ≤ -(a ^ 2 / (4 * s)) := by
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right ht (by positivity)
  have hpre : (2 * Real.pi * s)⁻¹ = 2 * (2 * Real.pi * (2 * s))⁻¹ := by
    field_simp
  rw [e1, Real.exp_add, hpre]
  have hp : 0 ≤ (2 * Real.pi * (2 * s))⁻¹ := by positivity
  calc 2 * (2 * Real.pi * (2 * s))⁻¹ * (Real.exp (-t / (2 * (2 * s))) * Real.exp (-t / (4 * s)))
      ≤ 2 * (2 * Real.pi * (2 * s))⁻¹ * (Real.exp (-t / (2 * (2 * s))) *
          Real.exp (-(a ^ 2 / (4 * s)))) := by gcongr
    _ = _ := by ring

 

theorem one_sub_plZ_le (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    1 - plZ q ε hε ≤ 2 * Real.exp (-(plRad q ε ^ 2 / (8 * ε ^ 2))) := by
  set s := ε ^ 2 / 2
  have hs : 0 < s := by have := hε.1; positivity
  set a := plRad q ε / 2
  have ha : 0 ≤ a := (div_pos (plRad_pos q hε) two_pos).le
  have hk : a ^ 2 / (4 * s) = plRad q ε ^ 2 / (8 * ε ^ 2) := by
    simp only [a, s]; field_simp; ring
  have hi1 : Integrable (fun w => heatKernel s 0 w) := integrable_heatKernel _ hs 0
  have hi2 : Integrable (fun w => plTest q ε hε 0 w) :=
    (plTest q ε hε 0).continuous.integrable_of_hasCompactSupport (plTest q ε hε 0).hasCompactSupport
  have hi3 : Integrable (fun w => 2 * Real.exp (-(a ^ 2 / (4 * s))) * heatKernel (2 * s) 0 w) :=
    (integrable_heatKernel _ (by positivity) 0).const_mul _
  have e1 : 1 - plZ q ε hε = ∫ w, (heatKernel s 0 w - plTest q ε hε 0 w) := by
    rw [integral_sub hi1 hi2, integral_heatKernel s hs 0, plZ]
  rw [e1, ← hk]
  calc ∫ w, (heatKernel s 0 w - plTest q ε hε 0 w)
      ≤ ∫ w, 2 * Real.exp (-(a ^ 2 / (4 * s))) * heatKernel (2 * s) 0 w := by
        refine integral_mono (hi1.sub hi2) hi3 fun w => ?_
        simp only
        rw [plTest_apply]
        have hp := heatKernel_nonneg s hs.le 0 w
        by_cases hw : ‖w‖ ≤ a
        · rw [plBump_eq_one q ε hε (by rw [zero_sub, norm_neg]; exact hw), one_mul, sub_self]
          have := heatKernel_nonneg (2 * s) (by positivity) 0 w
          positivity
        · push Not at hw
          have hk2 := heatKernel_le_of_ge hs ha 0 w (by rw [zero_sub, norm_neg]; exact hw.le)
          have := plBump_nonneg q ε hε (0 - w)
          nlinarith
    _ = 2 * Real.exp (-(a ^ 2 / (4 * s))) := by
        rw [integral_const_mul, integral_heatKernel _ (by positivity) 0, mul_one]

end SupercriticalLQGUniqueness.B2.Polylog

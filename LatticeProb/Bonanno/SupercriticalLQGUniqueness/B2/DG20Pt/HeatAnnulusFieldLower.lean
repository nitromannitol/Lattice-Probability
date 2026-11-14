/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.HeatAnnulusFieldLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatPointOpenSmallLower
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_annulus_crossing_lower_of_field_bound
    (ξ : ℝ) (φ : ℂ → ℝ) (z : ℂ) (a b R M : ℝ)
    (hab : a < b)
    (hfield : ∀ x ∈ closedBall z R, |φ x| ≤ M) :
    ENNReal.ofReal (Real.exp (-(|ξ| * M)) * (b - a)) ≤
      crossLenIn ξ φ (closedBall z R) (sphere z a) (sphere z b) := by
  refine le_crossLenIn fun p hp => ?_
  obtain ⟨u, hu, v, hv, hpath, htrace⟩ := hp
  have hrad : b - a ≤ ‖v - u‖ := by
    have ht := dist_triangle v u z
    have hu' : dist u z = a := by
      simpa only [dist_comm] using (mem_sphere.mp hu)
    have hv' : dist v z = b := by
      simpa only [dist_comm] using (mem_sphere.mp hv)
    rw [hu', hv'] at ht
    rw [dist_eq_norm] at ht
    linarith
  calc
    ENNReal.ofReal (Real.exp (-(|ξ| * M)) * (b - a)) ≤
        ENNReal.ofReal (Real.exp (-(|ξ| * M)) * ‖v - u‖) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hrad (Real.exp_pos _).le)
    _ ≤ lfppLen ξ φ p :=
      lfppLen_ge hpath (fun t ht => hfield _ (htrace t ht))

end SupercriticalLQGUniqueness.B2.DG20Pt

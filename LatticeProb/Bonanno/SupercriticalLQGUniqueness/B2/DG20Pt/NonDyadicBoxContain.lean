/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBoxContain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicBoxCompare

 

set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem dg20_bounded_subset_ferniqueBox
    (U : Set ℂ) (hU : Bornology.IsBounded U) :
    ∃ x₀ : ℂ, ∃ b : ℝ, 0 < b ∧ U ⊆ ferniqueBox x₀ b := by
  obtain ⟨R₀, hR₀⟩ := hU.subset_ball (0 : ℂ)
  let R : ℝ := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  let x₀ : ℂ := ⟨-R, -R⟩
  refine ⟨x₀, 2 * R, by positivity, ?_⟩
  intro z hz
  have hzR : ‖z‖ < R := by
    have h := hR₀ hz
    simpa only [mem_ball, dist_zero_right] using
      (h.trans_le (le_max_left R₀ 1))
  have hre := (Complex.abs_re_le_norm z).trans_lt hzR
  have him := (Complex.abs_im_le_norm z).trans_lt hzR
  obtain ⟨hrelo, hrehi⟩ := abs_lt.mp hre
  obtain ⟨himlo, himhi⟩ := abs_lt.mp him
  change z.re ∈ Icc (-R) (-R + 2 * R) ∧
    z.im ∈ Icc (-R) (-R + 2 * R)
  constructor <;> constructor <;> linarith

end SupercriticalLQGUniqueness.B2.DG20Pt

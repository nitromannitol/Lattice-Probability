import LatticeProb.Analysis.IntervalDirichletUniqueness
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Classical angular uniqueness on a circular arc -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Two continuous functions on a closed circular arc agree when their angular
pullbacks are classical solutions with zero second derivative and the same
endpoint values. -/
theorem eqOn_circleMap_image_Icc_of_deriv_deriv_eq_zero {a b : ℝ} (hab : a < b)
    {F G : ℂ → ℝ}
    (hF : ContinuousOn F (circleMap 0 1 '' Icc a b))
    (hG : ContinuousOn G (circleMap 0 1 '' Icc a b))
    (hdF : DifferentiableOn ℝ (fun t => F (circleMap 0 1 t)) (Ioo a b))
    (hdG : DifferentiableOn ℝ (fun t => G (circleMap 0 1 t)) (Ioo a b))
    (hddF : ∀ x ∈ Ioo a b, HasDerivAt (deriv (fun t => F (circleMap 0 1 t))) 0 x)
    (hddG : ∀ x ∈ Ioo a b, HasDerivAt (deriv (fun t => G (circleMap 0 1 t))) 0 x)
    (ha : F (circleMap 0 1 a) = G (circleMap 0 1 a))
    (hb : F (circleMap 0 1 b) = G (circleMap 0 1 b)) :
    (circleMap 0 1 '' Icc a b).EqOn F G := by
  let f : ℝ → ℝ := fun t => F (circleMap 0 1 t)
  let g : ℝ → ℝ := fun t => G (circleMap 0 1 t)
  have hf : ContinuousOn f (Icc a b) := hF.comp (by fun_prop) (mapsTo_image _ _)
  have hg : ContinuousOn g (Icc a b) := hG.comp (by fun_prop) (mapsTo_image _ _)
  have hd : DifferentiableOn ℝ (fun t => f t - g t) (Ioo a b) := hdF.sub hdG
  have hdd : ∀ x ∈ Ioo a b, HasDerivAt (deriv (fun t => f t - g t)) 0 x := by
    intro x hx
    have heq : deriv (fun t => f t - g t) =ᶠ[𝓝 x] fun t => deriv f t - deriv g t := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
      exact deriv_sub ((hdF t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
        ((hdG t ht).differentiableAt (isOpen_Ioo.mem_nhds ht))
    have h := (hddF x hx).sub (hddG x hx)
    change HasDerivAt (fun t => deriv f t - deriv g t) (0 - 0) x at h
    rw [sub_self] at h
    exact h.congr_of_eventuallyEq heq
  have hz := eq_zero_on_Icc_of_deriv_deriv_eq_zero hab (hf.sub hg) hd hdd
    (sub_eq_zero.mpr ha) (sub_eq_zero.mpr hb)
  rintro z ⟨x, hx, rfl⟩
  exact sub_eq_zero.mp (hz x hx)

end LatticeProb

import LatticeProb.Analysis.IntervalDirichletSineCoefficients
import LatticeProb.Analysis.WedgeArcSineClosureSpecialization
import LatticeProb.Analysis.WedgeArcWeakEigenfunction

/-! # Classical Dirichlet functions in the angular sine graph -/

set_option autoImplicit false

open MeasureTheory Set Metric
open LQGMetric.HeatSq

namespace LatticeProb

/-- Real classical Dirichlet data and its negative second derivative, viewed as
complex L² classes on the arc, belong to the closure of the angular sine graph. -/
theorem wedgeArc_classical_mem_sineGraph_closure {θ : ℝ}
    (hθ : 0 < θ) (hθ' : θ ≤ 2 * Real.pi)
    {f f' f'' : ℝ → ℝ} (hf : Continuous f) (hf'' : Continuous f'')
    (hf' : ContinuousOn f' (Icc (-θ / 2) (θ / 2)))
    (hfd : ∀ t ∈ Ioo (-θ / 2) (θ / 2), HasDerivAt f (f' t) t)
    (hf'd : ∀ t ∈ Ioo (-θ / 2) (θ / 2), HasDerivAt f' (f'' t) t)
    (ha : f (-θ / 2) = 0) (hb : f (θ / 2) = 0)
    (x y : Lp ℂ 2 (wedgeArcSurfaceMeasure θ))
    (hx : (fun z => x z) =ᵐ[wedgeArcSurfaceMeasure θ]
      fun z => (f (Complex.arg z) : ℂ))
    (hy : (fun z => y z) =ᵐ[wedgeArcSurfaceMeasure θ]
      fun z => (-f'' (Complex.arg z) : ℝ)) :
    (x, y) ∈ (wedgeArcSinePMap hθ hθ').graph.topologicalClosure := by
  apply (wedgeArcSinePMap_graph_closure_iff hθ hθ' x y).2
  intro n
  let s : ℝ → ℝ := fun t => Real.sqrt (2 / θ) * sinMode (-θ / 2) θ (n + 1) t
  have hs : Continuous s := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_const_mul_sinMode _ _ _ _ t).continuousAt
  have hi (u : Lp ℂ 2 (wedgeArcSurfaceMeasure θ)) (g : ℝ → ℝ)
      (hg : Continuous g) (hu : (fun z => u z) =ᵐ[wedgeArcSurfaceMeasure θ]
        fun z => (g (Complex.arg z) : ℂ)) :
      inner ℂ (wedgeArcSineLp θ n) u =
        ((∫ t in (-θ / 2)..(θ / 2), s t * g t : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    have heq : (fun z => inner ℂ (wedgeArcSineLp θ n z) (u z)) =ᵐ[wedgeArcSurfaceMeasure θ]
        (fun z : sphere (0 : ℂ) 1 => ((s (Complex.arg z) * g (Complex.arg z) : ℝ) : ℂ)) := by
      filter_upwards [(wedgeArcSineMode_memLp θ n).coeFn_toLp, hu] with z hz hzu
      change wedgeArcSineLp θ n z = _ at hz
      rw [hz, hzu]
      simp [wedgeArcSineMode, s, RCLike.inner_apply, ← Complex.ofReal_mul, mul_comm]
    rw [integral_congr_ae heq, integral_complex_ofReal]
    congr 1
    exact integral_arg_wedgeArcSurfaceMeasure hθ hθ' (hs.mul hg)
  rw [hi y (fun t => -f'' t) hf''.neg hy, hi x f hf hx]
  have he : -θ / 2 + θ = θ / 2 := by ring
  have hc := interval_sine_coefficient_neg_second_deriv (a := -θ / 2)
    (L := θ) (c := Real.sqrt (2 / θ)) hθ (n + 1)
    (by simpa only [he] using hf.continuousOn)
    (by simpa only [he] using hf')
    (by simpa only [he] using hf''.continuousOn)
    (by simpa only [he] using hfd) (by simpa only [he] using hf'd)
    ha (by simpa only [he] using hb)
  have hc' : (∫ t in (-θ / 2)..(θ / 2), s t * -f'' t) =
      (Real.pi * (n + 1 : ℕ) / θ) ^ 2 * ∫ t in (-θ / 2)..(θ / 2), s t * f t := by
    simpa only [he] using hc
  rw [hc']
  push_cast
  rfl

end LatticeProb

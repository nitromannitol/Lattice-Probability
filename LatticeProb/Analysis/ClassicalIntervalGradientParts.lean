import LatticeProb.Analysis.ClassicalIntervalGradient
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Integration by parts for the classical interval gradient -/

set_option autoImplicit false

open MeasureTheory Set

namespace LatticeProb

/-- Integration by parts for a zero-boundary function with an L² classical
derivative and a test function with integrable derivative. -/
theorem integral_mul_deriv_eq_neg_of_memLp_deriv
    {f f' v v' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hvd : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hfi : MemLp f' 2 (volume.restrict (Ioo a b)))
    (hvi : IntervalIntegrable v' volume a b) (ha : f a = 0) (hb : f b = 0) :
    (∫ x in a..b, f x * v' x) = -(∫ x in a..b, f' x * v x) := by
  have hfi' : IntervalIntegrable f' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 (hfi.integrable (by norm_num))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (by simpa [uIcc_of_le hab.le] using hf)
    (by simpa [uIcc_of_le hab.le] using hv)
    (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hfd)
    (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hvd) hfi' hvi
  simpa [ha, hb] using h

/-- The representatives of each graph element satisfy the same weak identity. -/
theorem classicalIntervalGradientGraph_parts
    {a b : ℝ} (hab : a < b)
    (p : Lp ℂ 2 (volume.restrict (Ioo a b)) × Lp ℂ 2 (volume.restrict (Ioo a b)))
    (hp : p ∈ classicalIntervalGradientGraph a b)
    {v v' : ℝ → ℂ} (hv : ContinuousOn v (Icc a b))
    (hvd : ∀ x ∈ Ioo a b, HasDerivAt v (v' x) x)
    (hvi : IntervalIntegrable v' volume a b) :
    ∃ f g : ℝ → ℂ,
      (fun x => p.1 x) =ᵐ[volume.restrict (Ioo a b)] f ∧
      (fun x => p.2 x) =ᵐ[volume.restrict (Ioo a b)] g ∧
      (∫ x in a..b, f x * v' x) = -(∫ x in a..b, g x * v x) := by
  obtain ⟨f, g, hf, hg, hc, ha, hb, hd⟩ := hp
  refine ⟨f, g, hf, hg, ?_⟩
  exact integral_mul_deriv_eq_neg_of_memLp_deriv hab hc hv hd hvd
    ((memLp_congr_ae hg).mp (Lp.memLp p.2)) hvi ha hb

end LatticeProb

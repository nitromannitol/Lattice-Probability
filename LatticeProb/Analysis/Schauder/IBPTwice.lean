import LatticeProb.Analysis.Schauder.IBPKernel
import LatticeProb.Analysis.Schauder.BoundedDerivs

/-!
# Moving two derivatives onto an integrable kernel

Applying the integration by parts of `IBPKernel` twice moves a pair of directional derivatives
from a bounded `C²` function `v` onto an integrable `C²` kernel `K` with integrable derivatives up
to order two:
`∫ K(y) (∂_u ∂_w v)(x - y) dy = ∫ (∂_w ∂_u K)(y) v(x - y) dy`.
The first step moves `∂_u` from `∂_w v` onto `K`, the second moves `∂_w` from `v` onto `∂_u K`.
-/

namespace LatticeProb.Analysis.Schauder

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Two integrations by parts move both derivatives of a bounded `C²` function onto an integrable
`C²` kernel: `∫ K(y) ∂_u∂_w v(x − y) dy = ∫ ∂_w∂_u K(y) v(x − y) dy`. -/
theorem integral_mul_dirDeriv_dirDeriv_comp_sub {K v : Euc d → ℝ}
    (hK : ContDiff ℝ 2 K) (hK0 : Integrable K) (hK1 : ∀ e : Euc d, Integrable (dirDeriv e K))
    (hK2 : ∀ e e' : Euc d, Integrable (dirDeriv e' (dirDeriv e K)))
    (hv : BoundedDerivs 2 v) (x u w : Euc d) :
    ∫ y, K y * dirDeriv u (dirDeriv w v) (x - y) =
      ∫ y, dirDeriv w (dirDeriv u K) y * v (x - y) := by
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  have hKu : Differentiable ℝ (dirDeriv u K) :=
    ((hK.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable one_ne_zero
  have hg : BoundedDerivs 1 (dirDeriv w v) := hv.dirDeriv w
  obtain ⟨A, hA⟩ := hg.exists_abs_le
  obtain ⟨B, hB⟩ := hg.exists_norm_fderiv_le
  have step1 : ∫ y, K y * dirDeriv u (dirDeriv w v) (x - y) =
      ∫ y, dirDeriv u K y * dirDeriv w v (x - y) :=
    integral_mul_fderiv_comp_sub_eq hKd hK0 (fun e => hK1 e) hg.differentiable hg.continuous
      hg.continuous_fderiv hA hB x u
  obtain ⟨A', hA'⟩ := hv.exists_abs_le
  obtain ⟨B', hB'⟩ := hv.exists_norm_fderiv_le
  have step2 : ∫ y, dirDeriv u K y * dirDeriv w v (x - y) =
      ∫ y, dirDeriv w (dirDeriv u K) y * v (x - y) :=
    integral_mul_fderiv_comp_sub_eq hKu (hK1 u) (fun e => hK2 u e) hv.differentiable
      hv.continuous hv.continuous_fderiv hA' hB' x w
  exact step1.trans step2

end

end LatticeProb.Analysis.Schauder

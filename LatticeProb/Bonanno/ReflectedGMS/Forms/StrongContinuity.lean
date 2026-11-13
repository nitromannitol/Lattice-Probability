/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StrongContinuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventRange
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! The existing equicontinuity theorem extends convergence on a dense range.
The weighted spectral estimate needed on that range is an explicit hypothesis
here; this lemma alone does not construct the semigroup. -/

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace ReflectedGMS.FullNetworkForm

/-- Contractions converging to the identity on a dense range converge on every
vector. The approximation argument is mathlib's equicontinuity/closure theorem. -/
theorem contraction_tendsto_of_denseRange
    {𝕜 E D ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (l : Filter ι) (S : ι → E →L[𝕜] E) (R : D → E)
    (hS : ∀ i, ‖S i‖ ≤ 1) (hR : DenseRange R)
    (hlim : ∀ y, Tendsto (fun i => S i (R y)) l (𝓝 (R y))) (x : E) :
    Tendsto (fun i => S i x) l (𝓝 x) := by
  have heq : Equicontinuous (fun i => (S i : E → E)) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun i =>
      (S i).lipschitzWith.weaken (show ‖S i‖₊ ≤ 1 from hS i)).equicontinuous
  exact (heq x).tendsto_of_mem_closure
    (f := id) (s := Set.range R) continuousWithinAt_id
    (by rintro y ⟨z, rfl⟩; exact hlim z) (hR x)

/-- A time-linear error on a dense operator range suffices for strong continuity
at zero; no uniform operator-norm convergence to the identity is asserted. -/
theorem contraction_tendsto_of_range_error
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (S : ℝ≥0 → E →L[𝕜] E) (R : E →L[𝕜] E)
    (hS : ∀ t, ‖S t‖ ≤ 1) (hR : DenseRange R)
    (herror : ∀ t y, ‖S t (R y) - R y‖ ≤ (t : ℝ) * ‖y‖) (x : E) :
    Tendsto (fun t => S t x) (𝓝 0) (𝓝 x) := by
  apply contraction_tendsto_of_denseRange (𝓝 0) S R hS hR _ x
  intro y
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun t => herror t y)
  have hz : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝 0) (𝓝 0) :=
    NNReal.continuous_coe.continuousAt
  simpa using hz.mul_const ‖y‖

end ReflectedGMS.FullNetworkForm

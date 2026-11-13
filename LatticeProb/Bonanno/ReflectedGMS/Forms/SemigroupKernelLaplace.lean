/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupKernelLaplace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupAlphaLaplace
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupKernel

/-! Scalar Laplace transforms of the actual analytic vertex kernel, obtained
directly by bounded coordinate evaluation of the operator integral. -/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

private noncomputable def vertexEvaluation (m : V → ℝ) (x : V) :
    ValueSpace V →L[ℝ] ℝ :=
  (Real.sqrt (m x))⁻¹ • lp.evalCLM ℝ (fun _ : V => ℝ) 2 x

private theorem vertexEvaluation_apply (m : V → ℝ) (x : V) (u : ValueSpace V) :
    vertexEvaluation m x u = unweight m u x := by
  change (Real.sqrt (m x))⁻¹ * u x = u x / Real.sqrt (m x)
  rw [div_eq_mul_inv, mul_comm]

theorem integrableOn_exp_neg_alpha_mul_semigroupKernel
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    IntegrableOn (fun t : ℝ => Real.exp (-alpha * t) *
      semigroupKernel G m (Real.toNNReal t) x y) (Ioi 0) := by
  let u := weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)
  have hu : IntegrableOn (fun t : ℝ => Real.exp (-alpha * t) •
      fullFormSemigroup G m (Real.toNNReal t) u) (Ioi 0) := by
    exact (ContinuousLinearMap.apply ℝ (ValueSpace V) u).integrable_comp
      (integrableOn_exp_neg_alpha_smul_fullFormSemigroup G m ha)
  have hv := (vertexEvaluation m x).integrable_comp hu
  change Integrable (fun t : ℝ => Real.exp (-alpha * t) *
    semigroupKernel G m (Real.toNNReal t) x y) (volume.restrict (Ioi 0))
  convert hv using 1
  ext t
  simp only [Function.comp_def, map_smul, vertexEvaluation_apply,
    smul_eq_mul, semigroupKernel, u]

/-- The vertex-kernel transform equals the decoded full-domain resolvent at
the exact occupation normalization `(1/alpha) * R_(1/alpha)`. -/
theorem integral_exp_neg_alpha_mul_semigroupKernel
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    (∫ t : ℝ in Ioi 0, Real.exp (-alpha * t) *
      semigroupKernel G m (Real.toNNReal t) x y) =
      (1 / alpha) * unweight m
        (parameterizedResolvent G m (1 / alpha)
          (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))) x := by
  let u := weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y)
  have hu : IntegrableOn (fun t : ℝ => Real.exp (-alpha * t) •
      fullFormSemigroup G m (Real.toNNReal t) u) (Ioi 0) :=
    (ContinuousLinearMap.apply ℝ (ValueSpace V) u).integrable_comp
      (integrableOn_exp_neg_alpha_smul_fullFormSemigroup G m ha)
  have hv := (vertexEvaluation m x).integral_comp_comm hu
  rw [integral_exp_neg_alpha_smul_fullFormSemigroup_apply G m ha] at hv
  simpa only [Function.comp_def, map_smul, vertexEvaluation_apply,
    smul_eq_mul, semigroupKernel, u] using hv

end ReflectedGMS.FullNetworkForm

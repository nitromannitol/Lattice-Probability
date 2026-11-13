/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2SubdivLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2SubdivGreen

 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

 
def restrictInl : EuclideanSpace ℝ (SubV V E M) →L[ℝ] EuclideanSpace ℝ V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun v => x (Sum.inl v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem restrictInl_apply (x : EuclideanSpace ℝ (SubV V E M)) (v : V) :
    restrictInl M x v = x (Sum.inl v) := rfl

 
theorem gff_subdiv_map_restrict (hM : 2 ≤ M) (hK : Γ.toWired.precision.PosDef) :
    (Γ.subdiv M hM).toWired.gff.map (restrictInl M) = Γ.toWired.gff := by
  have hKM := Γ.subdiv_posDef M hM hK
  letI : IsGaussian ((Γ.subdiv M hM).toWired.gff) := by
    unfold WiredConductances.gff; infer_instance
  letI : IsGaussian ((Γ.subdiv M hM).toWired.gff.map (restrictInl M)) := by infer_instance
  apply IsGaussian.ext
  · simp only [id]
    rw [(restrictInl (V := V) (E := E) M).integral_id_map IsGaussian.integrable_id]
    simp [WiredConductances.gff, integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun V ℝ).toBasis fun v w => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
  have hcoord (v : V) :
      (fun h : EuclideanSpace ℝ V =>
        inner ℝ ((EuclideanSpace.basisFun V ℝ).toBasis v) h) = (fun h => h v) := by
    ext h
    simp [PiLp.inner_apply]
  rw [hcoord v, hcoord w, covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  simp only [restrictInl_apply]
  unfold WiredConductances.gff
  rw [covariance_eval_multivariateGaussian hKM.inv.posSemidef,
    covariance_eval_multivariateGaussian hK.inv.posSemidef]
  exact Γ.green_subdiv_inl M hM hK v w
  all_goals exact IsGaussian.memLp_two_id

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos

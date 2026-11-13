/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFBoxSplitGaussian at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxMarkovAlgebra
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos

 
def boxSplitFieldEquiv (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] (e : DGFFSite n ≃ I ⊕ O) :
    EuclideanSpace ℝ (DGFFSite n) ≃L[ℝ]
      EuclideanSpace ℝ I × EuclideanSpace ℝ O :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toContinuousLinearEquiv.trans
    EuclideanSpace.sumEquivProd

theorem boxSplitField_apply_left (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) (i : I) :
    (boxSplitFieldEquiv n e h).1 i = h (e.symm (Sum.inl i)) := rfl

theorem boxSplitField_apply_right (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) (j : O) :
    (boxSplitFieldEquiv n e h).2 j = h (e.symm (Sum.inr j)) := rfl

theorem boxSplitField_covariance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (α β : I ⊕ O) :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) =>
        Sum.elim (boxSplitFieldEquiv n e h).1
          (boxSplitFieldEquiv n e h).2 α,
      fun h : EuclideanSpace ℝ (DGFFSite n) =>
        Sum.elim (boxSplitFieldEquiv n e h).1
          (boxSplitFieldEquiv n e h).2 β; boxDGFF n] =
      (boxSplitPrecision n e)⁻¹ α β := by
  have hcoord (γ : I ⊕ O) :
      (fun h : EuclideanSpace ℝ (DGFFSite n) =>
        Sum.elim (boxSplitFieldEquiv n e h).1
          (boxSplitFieldEquiv n e h).2 γ) =
      (fun h => h (e.symm γ)) := by
    ext h
    cases γ with
    | inl i => exact boxSplitField_apply_left n e h i
    | inr j => exact boxSplitField_apply_right n e h j
  rw [hcoord α, hcoord β]
  change cov[fun h : EuclideanSpace ℝ (DGFFSite n) => h (e.symm α),
    fun h : EuclideanSpace ℝ (DGFFSite n) => h (e.symm β);
    multivariateGaussian 0 (boxConductances n).precision⁻¹] = _
  rw [covariance_eval_multivariateGaussian (box_precision_posDef n).inv.posSemidef]
  change (boxConductances n).precision⁻¹ (e.symm α) (e.symm β) =
    (Matrix.reindex e e (boxConductances n).precision)⁻¹ α β
  rw [Matrix.inv_reindex]
  rfl

end SupercriticalLQGUniqueness.B2.QPos

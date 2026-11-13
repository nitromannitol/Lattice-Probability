/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFMarkovLaw at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFMarkovResidual

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

def boxResidualInnerCLM (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    EuclideanSpace ℝ (DGFFSite n) →L[ℝ] EuclideanSpace ℝ I :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ I)
    (EuclideanSpace ℝ O)).comp (boxResidualFieldCLM n e)

theorem boxResidualInnerCLM_apply (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) :
    boxResidualInnerCLM n e h = (boxResidualField n e h).1 := rfl

def boxResidualInnerLaw (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) : Measure (EuclideanSpace ℝ I) :=
  (boxDGFF n).map (boxResidualInnerCLM n e)

instance boxResidualInnerLaw_isGaussian (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) : IsGaussian (boxResidualInnerLaw n e) := by
  unfold boxResidualInnerLaw
  have hG := (boxResidualField_hasGaussianLaw n e).fst
  change IsGaussian ((boxDGFF n).map (fun h => (boxResidualField n e h).1))
  exact hG.isGaussian_map

end SupercriticalLQGUniqueness.B2.QPos

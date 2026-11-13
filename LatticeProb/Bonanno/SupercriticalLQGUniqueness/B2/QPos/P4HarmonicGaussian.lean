/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4HarmonicGaussian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4CoarseCovariance
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFMarkovLaw

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos

def boxHarmonicFieldCLM (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    EuclideanSpace ℝ (DGFFSite n) →L[ℝ] EuclideanSpace ℝ I :=
  ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ I)
    (EuclideanSpace ℝ O)).comp
      (boxSplitFieldEquiv n e).toContinuousLinearMap) -
    boxResidualInnerCLM n e

theorem boxHarmonicFieldCLM_apply (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) (i : I) :
    boxHarmonicFieldCLM n e h i = boxHarmonicField n e h i := rfl

theorem boxHarmonicField_hasGaussianLaw (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    HasGaussianLaw (fun h : EuclideanSpace ℝ (DGFFSite n) =>
      boxHarmonicFieldCLM n e h) (boxDGFF n) := by
  have hG : HasGaussianLaw (fun h : EuclideanSpace ℝ (DGFFSite n) => h)
      (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    exact IsGaussian.hasGaussianLaw_id
  exact hG.map_fun (boxHarmonicFieldCLM n e)

theorem boxHarmonicField_mean_zero (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    ∫ h : EuclideanSpace ℝ (DGFFSite n),
      boxHarmonicFieldCLM n e h ∂(boxDGFF n) = 0 := by
  have hG : IsGaussian (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    infer_instance
  have hi : Integrable (fun h : EuclideanSpace ℝ (DGFFSite n) => h)
      (boxDGFF n) := IsGaussian.integrable_id
  calc
    _ = (boxHarmonicFieldCLM n e)
        (∫ h : EuclideanSpace ℝ (DGFFSite n), h ∂boxDGFF n) := by
          exact (boxHarmonicFieldCLM n e).integral_comp_comm
            hi
    _ = 0 := by rw [boxDGFF_mean]; simp

theorem boxHarmonicField_mean_zero_coord (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (i : I) :
    ∫ h : EuclideanSpace ℝ (DGFFSite n),
      boxHarmonicField n e h i ∂(boxDGFF n) = 0 := by
  have hG : IsGaussian (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    infer_instance
  have hi : Integrable (fun h : EuclideanSpace ℝ (DGFFSite n) => h)
      (boxDGFF n) := IsGaussian.integrable_id
  have hh : Integrable (fun h => boxHarmonicFieldCLM n e h)
      (boxDGFF n) := (boxHarmonicFieldCLM n e).integrable_comp hi
  have hp := (EuclideanSpace.proj i).integral_comp_comm hh
  change (∫ h : EuclideanSpace ℝ (DGFFSite n),
    boxHarmonicFieldCLM n e h i ∂(boxDGFF n)) =
      (∫ h : EuclideanSpace ℝ (DGFFSite n),
        boxHarmonicFieldCLM n e h ∂(boxDGFF n)) i at hp
  rw [boxHarmonicField_mean_zero n e] at hp
  simpa [boxHarmonicFieldCLM_apply] using hp

end SupercriticalLQGUniqueness.B2.QPos

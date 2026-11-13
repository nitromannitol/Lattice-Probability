/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFMarkovResidual at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxSplitGaussian
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Analysis.CStarAlgebra.Matrix

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

 

def boxResidualMatrix (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    Matrix (I ⊕ O) (I ⊕ O) ℝ :=
  let H := boxSplitPrecision n e
  Matrix.fromBlocks 1 (H.toBlocks₁₁⁻¹ * H.toBlocks₁₂) 0 1

 
def boxResidualField (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    EuclideanSpace ℝ (DGFFSite n) →
      EuclideanSpace ℝ I × EuclideanSpace ℝ O :=
  fun h => EuclideanSpace.sumEquivProd
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (boxResidualMatrix n e)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e) h))

 
def boxResidualFieldCLM (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    EuclideanSpace ℝ (DGFFSite n) →L[ℝ]
      EuclideanSpace ℝ I × EuclideanSpace ℝ O :=
  EuclideanSpace.sumEquivProd.toContinuousLinearMap.comp
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (boxResidualMatrix n e)).comp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toContinuousLinearMap)

theorem boxResidualField_hasGaussianLaw (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    HasGaussianLaw (boxResidualField n e) (boxDGFF n) := by
  have hG : HasGaussianLaw (fun h : EuclideanSpace ℝ (DGFFSite n) => h)
      (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    exact IsGaussian.hasGaussianLaw_id
  exact (hG.map_equiv_fun
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).toContinuousLinearEquiv).map_fun
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (boxResidualMatrix n e)) |>.map_equiv_fun
        EuclideanSpace.sumEquivProd

theorem boxResidualField_apply_left (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) (i : I) :
    (boxResidualField n e h).1 i =
      (boxSplitFieldEquiv n e h).1 i +
        ∑ j : O, ((boxSplitPrecision n e).toBlocks₁₁⁻¹ *
          (boxSplitPrecision n e).toBlocks₁₂) i j *
          (boxSplitFieldEquiv n e h).2 j := by
  simp [boxResidualField, boxResidualMatrix, boxSplitFieldEquiv,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, Matrix.fromBlocks,
    dotProduct, Matrix.one_apply]

theorem boxResidualField_apply_right (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) (j : O) :
    (boxResidualField n e h).2 j = (boxSplitFieldEquiv n e h).2 j := by
  simp [boxResidualField, boxResidualMatrix, boxSplitFieldEquiv,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, Matrix.fromBlocks,
    dotProduct, Matrix.one_apply]

theorem boxDGFF_eval_memLp_two (n : ℕ) (z : DGFFSite n) :
    MemLp (fun h : EuclideanSpace ℝ (DGFFSite n) => h z) 2 (boxDGFF n) := by
  have hG : HasGaussianLaw (fun h : EuclideanSpace ℝ (DGFFSite n) => h)
      (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    exact IsGaussian.hasGaussianLaw_id
  simpa only [EuclideanSpace.coe_proj] using
    (hG.map_fun (EuclideanSpace.proj z)).memLp_two

 

theorem boxResidualField_cross_covariance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (i : I) (j : O) :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => (boxResidualField n e h).1 i,
      fun h : EuclideanSpace ℝ (DGFFSite n) => (boxResidualField n e h).2 j;
      boxDGFF n] = 0 := by
  let H := boxSplitPrecision n e
  let A := H.toBlocks₁₁
  let B := H.toBlocks₁₂
  let X : I → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun i h => (boxSplitFieldEquiv n e h).1 i
  let Y : O → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun j h => (boxSplitFieldEquiv n e h).2 j
  have hX (k : I) : MemLp (X k) 2 (boxDGFF n) := by
    simpa [X, boxSplitField_apply_left] using
      boxDGFF_eval_memLp_two n (e.symm (Sum.inl k))
  have hY (k : O) : MemLp (Y k) 2 (boxDGFF n) := by
    simpa [Y, boxSplitField_apply_right] using
      boxDGFF_eval_memLp_two n (e.symm (Sum.inr k))
  have hterm (k : O) :
      MemLp (fun h => (A⁻¹ * B) i k * Y k h) 2 (boxDGFF n) :=
    (hY k).const_mul _
  have hsum : MemLp (fun h => ∑ k : O, (A⁻¹ * B) i k * Y k h)
      2 (boxDGFF n) := by
    have heq : (∑ k : O, fun h => (A⁻¹ * B) i k * Y k h) =
        (fun h => ∑ k : O, (A⁻¹ * B) i k * Y k h) := by
      funext h
      simp only [Finset.sum_apply]
    rw [← heq]
    exact memLp_finsetSum' Finset.univ (fun k _ => hterm k)
  have hcov (α β : I ⊕ O) :
      cov[Sum.elim X Y α, Sum.elim X Y β; boxDGFF n] = H⁻¹ α β := by
    have heq (γ : I ⊕ O) : Sum.elim X Y γ =
        (fun h => Sum.elim (boxSplitFieldEquiv n e h).1
          (boxSplitFieldEquiv n e h).2 γ) := by
      cases γ <;> rfl
    rw [heq α, heq β]
    exact boxSplitField_covariance n e α β
  have hblock := (box_schur_markov_covariance n e).1
  change (H⁻¹).toBlocks₁₂ + A⁻¹ * B * (H⁻¹).toBlocks₂₂ = 0 at hblock
  rw [show (fun h => (boxResidualField n e h).1 i) =
      X i + fun h => ∑ k : O, (A⁻¹ * B) i k * Y k h from by
        funext h; exact boxResidualField_apply_left n e h i,
    show (fun h => (boxResidualField n e h).2 j) = Y j from by
      funext h; exact boxResidualField_apply_right n e h j]
  rw [covariance_add_left (hX i) hsum (hY j)]
  rw [covariance_fun_sum_left (fun k => hterm k) (hY j)]
  simp_rw [covariance_const_mul_left]
  simp_rw [show ∀ k : O, cov[Y k, Y j; boxDGFF n] = (H⁻¹).toBlocks₂₂ k j from by
    intro k; simpa [Matrix.toBlocks₂₂] using hcov (Sum.inr k) (Sum.inr j)]
  rw [show cov[X i, Y j; boxDGFF n] = (H⁻¹).toBlocks₁₂ i j from by
    simpa [Matrix.toBlocks₁₂] using hcov (Sum.inl i) (Sum.inr j)]
  change ((H⁻¹).toBlocks₁₂ + (A⁻¹ * B) * (H⁻¹).toBlocks₂₂) i j = 0
  rw [hblock]
  rfl

 

theorem boxResidualField_inner_raw_covariance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (i j : I) :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => (boxResidualField n e h).1 i,
      fun h : EuclideanSpace ℝ (DGFFSite n) => (boxSplitFieldEquiv n e h).1 j;
      boxDGFF n] =
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j := by
  let H := boxSplitPrecision n e
  let A := H.toBlocks₁₁
  let B := H.toBlocks₁₂
  let X : I → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun i h => (boxSplitFieldEquiv n e h).1 i
  let Y : O → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun j h => (boxSplitFieldEquiv n e h).2 j
  have hX (k : I) : MemLp (X k) 2 (boxDGFF n) := by
    simpa [X, boxSplitField_apply_left] using
      boxDGFF_eval_memLp_two n (e.symm (Sum.inl k))
  have hY (k : O) : MemLp (Y k) 2 (boxDGFF n) := by
    simpa [Y, boxSplitField_apply_right] using
      boxDGFF_eval_memLp_two n (e.symm (Sum.inr k))
  have hterm (k : O) :
      MemLp (fun h => (A⁻¹ * B) i k * Y k h) 2 (boxDGFF n) :=
    (hY k).const_mul _
  have hsum : MemLp (fun h => ∑ k : O, (A⁻¹ * B) i k * Y k h)
      2 (boxDGFF n) := by
    have heq : (∑ k : O, fun h => (A⁻¹ * B) i k * Y k h) =
        (fun h => ∑ k : O, (A⁻¹ * B) i k * Y k h) := by
      funext h
      simp only [Finset.sum_apply]
    rw [← heq]
    exact memLp_finsetSum' Finset.univ (fun k _ => hterm k)
  have hcov (α β : I ⊕ O) :
      cov[Sum.elim X Y α, Sum.elim X Y β; boxDGFF n] = H⁻¹ α β := by
    have heq (γ : I ⊕ O) : Sum.elim X Y γ =
        (fun h => Sum.elim (boxSplitFieldEquiv n e h).1
          (boxSplitFieldEquiv n e h).2 γ) := by
      cases γ <;> rfl
    rw [heq α, heq β]
    exact boxSplitField_covariance n e α β
  have hblock := (box_schur_markov_covariance n e).2
  change (H⁻¹).toBlocks₁₁ + A⁻¹ * B * (H⁻¹).toBlocks₂₁ = A⁻¹ at hblock
  rw [show (fun h => (boxResidualField n e h).1 i) =
      X i + fun h => ∑ k : O, (A⁻¹ * B) i k * Y k h from by
        funext h; exact boxResidualField_apply_left n e h i]
  change cov[X i + (fun h => ∑ k : O, (A⁻¹ * B) i k * Y k h),
    X j; boxDGFF n] = A⁻¹ i j
  rw [covariance_add_left (hX i) hsum (hX j)]
  rw [covariance_fun_sum_left (fun k => hterm k) (hX j)]
  simp_rw [covariance_const_mul_left]
  simp_rw [show ∀ k : O, cov[Y k, X j; boxDGFF n] = (H⁻¹).toBlocks₂₁ k j from by
    intro k; simpa [Matrix.toBlocks₂₁] using hcov (Sum.inr k) (Sum.inl j)]
  rw [show cov[X i, X j; boxDGFF n] = (H⁻¹).toBlocks₁₁ i j from by
    simpa [Matrix.toBlocks₁₁] using hcov (Sum.inl i) (Sum.inl j)]
  change ((H⁻¹).toBlocks₁₁ + (A⁻¹ * B) * (H⁻¹).toBlocks₂₁) i j = A⁻¹ i j
  rw [hblock]

 

theorem boxResidualField_inner_covariance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (i j : I) :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => (boxResidualField n e h).1 i,
      fun h : EuclideanSpace ℝ (DGFFSite n) => (boxResidualField n e h).1 j;
      boxDGFF n] =
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j := by
  let A := (boxSplitPrecision n e).toBlocks₁₁
  let B := (boxSplitPrecision n e).toBlocks₁₂
  let R : I → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun i h => (boxResidualField n e h).1 i
  let X : I → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun i h => (boxSplitFieldEquiv n e h).1 i
  let Y : O → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun j h => (boxSplitFieldEquiv n e h).2 j
  have hG := boxResidualField_hasGaussianLaw n e
  have hR (k : I) : MemLp (R k) 2 (boxDGFF n) := by
    have hh := (hG.fst.map_fun (EuclideanSpace.proj k)).memLp_two
    change MemLp (R k) 2 (boxDGFF n) at hh
    exact hh
  have hX (k : I) : MemLp (X k) 2 (boxDGFF n) := by
    simpa [X, boxSplitField_apply_left] using
      boxDGFF_eval_memLp_two n (e.symm (Sum.inl k))
  have hY (k : O) : MemLp (Y k) 2 (boxDGFF n) := by
    simpa [Y, boxSplitField_apply_right] using
      boxDGFF_eval_memLp_two n (e.symm (Sum.inr k))
  have hterm (k : O) :
      MemLp (fun h => (A⁻¹ * B) j k * Y k h) 2 (boxDGFF n) :=
    (hY k).const_mul _
  have hsum : MemLp (fun h => ∑ k : O, (A⁻¹ * B) j k * Y k h)
      2 (boxDGFF n) := by
    have heq : (∑ k : O, fun h => (A⁻¹ * B) j k * Y k h) =
        (fun h => ∑ k : O, (A⁻¹ * B) j k * Y k h) := by
      funext h
      simp only [Finset.sum_apply]
    rw [← heq]
    exact memLp_finsetSum' Finset.univ (fun k _ => hterm k)
  rw [show (fun h => (boxResidualField n e h).1 j) =
      X j + fun h => ∑ k : O, (A⁻¹ * B) j k * Y k h from by
        funext h; exact boxResidualField_apply_left n e h j]
  change cov[R i, X j + (fun h => ∑ k : O, (A⁻¹ * B) j k * Y k h);
    boxDGFF n] = A⁻¹ i j
  rw [covariance_add_right (hR i) (hX j) hsum]
  rw [covariance_fun_sum_right (fun k => hterm k) (hR i)]
  simp_rw [covariance_const_mul_right]
  simp_rw [show ∀ k : O, cov[R i, Y k; boxDGFF n] = 0 from by
    intro k
    have heq : Y k = fun h => (boxResidualField n e h).2 k := by
      funext h
      exact (boxResidualField_apply_right n e h k).symm
    rw [heq]
    exact boxResidualField_cross_covariance n e i k]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  exact boxResidualField_inner_raw_covariance n e i j

 

theorem boxResidualField_indep (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    IndepFun (fun h : EuclideanSpace ℝ (DGFFSite n) => (boxResidualField n e h).1)
      (fun h : EuclideanSpace ℝ (DGFFSite n) => (boxResidualField n e h).2)
      (boxDGFF n) := by
  have hR := boxResidualField_hasGaussianLaw n e
  apply hR.indepFun_of_covariance_inner
  intro x y
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x,
    ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial,
      EuclideanSpace.basisFun_inner]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [covariance_const_mul_left, covariance_const_mul_right]
    change x i * (y j * cov[fun h : EuclideanSpace ℝ (DGFFSite n) =>
      (boxResidualField n e h).1 i,
      fun h : EuclideanSpace ℝ (DGFFSite n) =>
      (boxResidualField n e h).2 j; boxDGFF n]) = 0
    rw [boxResidualField_cross_covariance, mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial,
      EuclideanSpace.basisFun_inner]
    intro i
    exact ((hR.fst.map_fun (EuclideanSpace.proj i)).memLp_two).const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial,
      EuclideanSpace.basisFun_inner]
    intro j
    exact ((hR.snd.map_fun (EuclideanSpace.proj j)).memLp_two).const_mul _

theorem box_inner_outer_residual_indep (n : ℕ)
    (U : Finset (DGFFSite n)) :
    IndepFun (fun h : EuclideanSpace ℝ (DGFFSite n) =>
        (boxResidualField n (boxInnerOuterEquiv n U) h).1)
      (fun h : EuclideanSpace ℝ (DGFFSite n) =>
        (boxResidualField n (boxInnerOuterEquiv n U) h).2)
      (boxDGFF n) :=
  boxResidualField_indep n (boxInnerOuterEquiv n U)

end SupercriticalLQGUniqueness.B2.QPos

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4CoarseCovariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFMarkovResidual

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

 
def boxHarmonicField (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) (i : I) : ℝ :=
  (boxSplitFieldEquiv n e h).1 i - (boxResidualField n e h).1 i

 

theorem boxHarmonicField_covariance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (i j : I) :
    cov[fun h : EuclideanSpace ℝ (DGFFSite n) => boxHarmonicField n e h i,
      fun h : EuclideanSpace ℝ (DGFFSite n) => boxHarmonicField n e h j;
      boxDGFF n] =
      (boxSplitPrecision n e)⁻¹ (Sum.inl i) (Sum.inl j) -
        (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j := by
  let X : I → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun i h => (boxSplitFieldEquiv n e h).1 i
  let R : I → EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun i h => (boxResidualField n e h).1 i
  have hX (k : I) : MemLp (X k) 2 (boxDGFF n) := by
    simpa [X, boxSplitField_apply_left] using
      boxDGFF_eval_memLp_two n (e.symm (Sum.inl k))
  have hR (k : I) : MemLp (R k) 2 (boxDGFF n) := by
    have hh := ((boxResidualField_hasGaussianLaw n e).fst.map_fun
      (EuclideanSpace.proj k)).memLp_two
    change MemLp (R k) 2 (boxDGFF n) at hh
    exact hh
  have hXR (k l : I) :
      cov[X k, R l; boxDGFF n] =
        (boxSplitPrecision n e).toBlocks₁₁⁻¹ l k := by
    rw [covariance_comm]
    exact boxResidualField_inner_raw_covariance n e l k
  have hsym : (boxSplitPrecision n e).toBlocks₁₁⁻¹ j i =
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j := by
    calc
      _ = cov[R j, R i; boxDGFF n] :=
        (boxResidualField_inner_covariance n e j i).symm
      _ = cov[R i, R j; boxDGFF n] := covariance_comm (R j) (R i)
      _ = _ := boxResidualField_inner_covariance n e i j
  change cov[X i - R i, X j - R j; boxDGFF n] = _
  rw [covariance_sub_sub (hX i) (hR i) (hX j) (hR j)]
  rw [show cov[X i, X j; boxDGFF n] =
      (boxSplitPrecision n e)⁻¹ (Sum.inl i) (Sum.inl j) from by
        exact boxSplitField_covariance n e (Sum.inl i) (Sum.inl j)]
  rw [hXR i j, boxResidualField_inner_raw_covariance,
    boxResidualField_inner_covariance, hsym]
  ring

 

theorem boxHarmonicField_increment_variance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (i j : I) :
    Var[fun h : EuclideanSpace ℝ (DGFFSite n) =>
      boxHarmonicField n e h i - boxHarmonicField n e h j; boxDGFF n] =
      ((boxSplitPrecision n e)⁻¹ (Sum.inl i) (Sum.inl i) +
        (boxSplitPrecision n e)⁻¹ (Sum.inl j) (Sum.inl j) -
        2 * (boxSplitPrecision n e)⁻¹ (Sum.inl i) (Sum.inl j)) -
      ((boxSplitPrecision n e).toBlocks₁₁⁻¹ i i +
        (boxSplitPrecision n e).toBlocks₁₁⁻¹ j j -
        2 * (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j) := by
  let Hi : EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun h => boxHarmonicField n e h i
  let Hj : EuclideanSpace ℝ (DGFFSite n) → ℝ :=
    fun h => boxHarmonicField n e h j
  have hmem (k : I) : MemLp (fun h : EuclideanSpace ℝ (DGFFSite n) =>
      boxHarmonicField n e h k) 2 (boxDGFF n) := by
    have hX := boxDGFF_eval_memLp_two n (e.symm (Sum.inl k))
    have hR := ((boxResidualField_hasGaussianLaw n e).fst.map_fun
      (EuclideanSpace.proj k)).memLp_two
    change MemLp (fun h => (boxResidualField n e h).1 k) 2 (boxDGFF n) at hR
    change MemLp (fun h =>
      h (e.symm (Sum.inl k)) - (boxResidualField n e h).1 k)
      2 (boxDGFF n)
    exact hX.sub hR
  have hi : MemLp Hi 2 (boxDGFF n) := hmem i
  have hj : MemLp Hj 2 (boxDGFF n) := hmem j
  change Var[Hi - Hj; boxDGFF n] = _
  rw [← covariance_self (hi.sub hj).aemeasurable,
    covariance_sub_sub hi hj hi hj]
  rw [show cov[Hi, Hi; boxDGFF n] =
      (boxSplitPrecision n e)⁻¹ (Sum.inl i) (Sum.inl i) -
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ i i from
        boxHarmonicField_covariance n e i i]
  rw [show cov[Hj, Hj; boxDGFF n] =
      (boxSplitPrecision n e)⁻¹ (Sum.inl j) (Sum.inl j) -
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ j j from
        boxHarmonicField_covariance n e j j]
  rw [show cov[Hi, Hj; boxDGFF n] =
      (boxSplitPrecision n e)⁻¹ (Sum.inl i) (Sum.inl j) -
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j from
        boxHarmonicField_covariance n e i j]
  rw [show cov[Hj, Hi; boxDGFF n] = cov[Hi, Hj; boxDGFF n] from
    covariance_comm Hj Hi]
  rw [show cov[Hi, Hj; boxDGFF n] =
      (boxSplitPrecision n e)⁻¹ (Sum.inl i) (Sum.inl j) -
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j from
        boxHarmonicField_covariance n e i j]
  ring

end SupercriticalLQGUniqueness.B2.QPos

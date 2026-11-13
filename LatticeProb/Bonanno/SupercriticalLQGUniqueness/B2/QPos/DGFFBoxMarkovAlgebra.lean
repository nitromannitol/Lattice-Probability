/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFBoxMarkovAlgebra at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFSchur
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFModel

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

open Matrix

 
def boxSplitPrecision (n : ℕ) {I O : Type*}
    (e : DGFFSite n ≃ I ⊕ O) : Matrix (I ⊕ O) (I ⊕ O) ℝ :=
  ((boxConductances n).precision).reindex e e

theorem boxSplitPrecision_posDef (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    (boxSplitPrecision n e).PosDef := by
  change (((boxConductances n).precision).submatrix e.symm e.symm).PosDef
  exact (box_precision_posDef n).submatrix e.symm.injective

theorem box_schur_markov_covariance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    let H := boxSplitPrecision n e
    let A := H.toBlocks₁₁
    let B := H.toBlocks₁₂
    let C := H.toBlocks₂₁
    let D := H.toBlocks₂₂
    (H⁻¹).toBlocks₁₂ + A⁻¹ * B * (H⁻¹).toBlocks₂₂ = 0 ∧
      (H⁻¹).toBlocks₁₁ + A⁻¹ * B * (H⁻¹).toBlocks₂₁ = A⁻¹ := by
  let H := boxSplitPrecision n e
  let A := H.toBlocks₁₁
  let B := H.toBlocks₁₂
  let C := H.toBlocks₂₁
  let D := H.toBlocks₂₂
  have hH : H.PosDef := boxSplitPrecision_posDef n e
  have hA : A.PosDef := by
    change H.toBlocks₁₁.PosDef
    convert hH.submatrix (e := Sum.inl) Sum.inl_injective using 1
    ext i j
    rfl
  letI : Invertible A := hA.isUnit.invertible
  have hb : fromBlocks A B C D = H := by
    simpa [A, B, C, D] using (fromBlocks_toBlocks H)
  letI : Invertible (fromBlocks A B C D) := by
    rw [hb]
    exact hH.isUnit.invertible
  letI : Invertible (D - C * ⅟A * B) :=
    Matrix.invertibleOfFromBlocks₁₁Invertible A B C D
  dsimp only
  constructor
  · simpa only [hb, invOf_eq_nonsing_inv] using dgff_schur_cross_zero A B C D
  · simpa only [hb, invOf_eq_nonsing_inv] using dgff_schur_inner_covariance A B C D

 
def boxInnerOuterEquiv (n : ℕ) (U : Finset (DGFFSite n)) :
    DGFFSite n ≃ {z : DGFFSite n // z ∈ U} ⊕
      {z : DGFFSite n // z ∉ U} :=
  (Equiv.sumCompl (fun z => z ∈ U)).symm

 

end SupercriticalLQGUniqueness.B2.QPos

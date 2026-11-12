/- Adapted from OpenAI's math repository (https://github.com/openai/math), commit 4eaee875,
   file lean/OAI/Probability/SpanningForest/PolynomialGramUpdate.lean, Apache License 2.0;
   changes: the module path is LatticeProb.OpenAI.Probability.SpanningForest.PolynomialGramUpdate in place of OAI.Probability.SpanningForest.PolynomialGramUpdate, and the module paths of local imports are changed in the same way; the import of LatticeProb.OpenAI.Probability.SpanningForest.GramDeterminantUpdate (not copied here) is replaced by the imports of the copied modules it reaches,
   namely ;
   the unused declarations `det_polynomial_gram_update` (they need modules not copied here) are omitted; statements and proofs of the declarations kept are unchanged. -/
import Mathlib

namespace OAI

noncomputable section

open scoped Matrix

namespace Problem336.Determinantal

variable {ν κ : Type*} [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]

theorem map_nonsing_inv_of_isUnit {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (L : Matrix ν ν R) (hL : IsUnit L.det) :
    (L.map φ)⁻¹ = L⁻¹.map φ := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hL]
  simp

theorem det_polynomial_rank_update
    (L : Matrix ν ν ℝ) (hL : IsUnit L.det)
    (U : Matrix ν κ ℝ) (V : Matrix κ ν ℝ) :
    (L.map Polynomial.C + (Polynomial.X : Polynomial ℝ) • (U * V).map Polynomial.C).det =
      Polynomial.C L.det *
        (1 + (Polynomial.X : Polynomial ℝ) • (V * L⁻¹ * U).map Polynomial.C).det := by
  have hdet : (L.map Polynomial.C).det = Polynomial.C L.det := by
    exact (Polynomial.C.map_det L).symm
  have hLC : IsUnit (L.map Polynomial.C).det := by
    rw [hdet]
    exact hL.map (Polynomial.C : ℝ →+* Polynomial ℝ)
  have h := Matrix.det_add_mul ((Polynomial.X : Polynomial ℝ) • U.map Polynomial.C)
    (V.map Polynomial.C) hLC
  rw [map_nonsing_inv_of_isUnit Polynomial.C L hL] at h
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul,
    hdet] using h


theorem det_polynomial_weighted_columns
    (L : Matrix ν ν ℝ) (hL : IsUnit L.det)
    (A : Matrix ν κ ℝ) (c : κ → ℝ) :
    (L.map Polynomial.C + (Polynomial.X : Polynomial ℝ) •
      (A * Matrix.diagonal c * A.transpose).map Polynomial.C).det =
      Polynomial.C L.det *
        (1 + (Polynomial.X : Polynomial ℝ) •
          (Matrix.diagonal c * (A.transpose * L⁻¹ * A)).map Polynomial.C).det := by
  simpa only [Matrix.mul_assoc] using
    det_polynomial_rank_update L hL A (Matrix.diagonal c * A.transpose)

end Problem336.Determinantal

end

end OAI

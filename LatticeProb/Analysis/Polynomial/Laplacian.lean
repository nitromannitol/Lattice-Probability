/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/PolynomialLaplacian.lean.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# The formal Laplacian of real polynomials and the squared-norm product identity

For real polynomials in `d` variables, `polynomialLaplacian p = ∑ᵢ ∂ᵢ ∂ᵢ p` is the formal Laplacian
and `polynomialSquaredNorm d = ∑ᵢ Xᵢ ^ 2` is the squared Euclidean norm about the origin. The file
shows that the formal Laplacian is additive and commutes with scalar multiplication, computes the
partial derivatives of `polynomialSquaredNorm d`, and proves the product identity
`Δ(|x|² p) = 2d · p + 4 ∑ᵢ Xᵢ ∂ᵢ p + |x|² Δp`.
-/

open MvPolynomial
namespace LatticeProb

/-- The formal Laplacian `∑ᵢ ∂ᵢ ∂ᵢ` of a real polynomial in `d` variables. -/
noncomputable def polynomialLaplacian {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    MvPolynomial (Fin d) ℝ := ∑ i, pderiv i (pderiv i p)

/-- The squared Euclidean norm `∑ᵢ Xᵢ ^ 2` of the coordinates, as a polynomial in `d` variables. -/
noncomputable def polynomialSquaredNorm (d : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ i, X i ^ 2

/-- The formal Laplacian is additive. -/
lemma polynomialLaplacian_add {d : ℕ} (p q : MvPolynomial (Fin d) ℝ) :
    polynomialLaplacian (p + q) = polynomialLaplacian p + polynomialLaplacian q := by
  simp [polynomialLaplacian, map_add, Finset.sum_add_distrib]

/-- The formal Laplacian commutes with scalar multiplication. -/
lemma polynomialLaplacian_smul {d : ℕ} (c : ℝ) (p : MvPolynomial (Fin d) ℝ) :
    polynomialLaplacian (c • p) = c • polynomialLaplacian p := by
  simp [polynomialLaplacian, Finset.smul_sum]

/-- The `i`-th formal partial derivative of the squared norm `∑ⱼ Xⱼ ^ 2` is `2 Xᵢ`. -/
lemma pderiv_polynomialSquaredNorm {d : ℕ} (i : Fin d) :
    pderiv i (polynomialSquaredNorm d) = 2 * X i := by
  classical
  rw [polynomialSquaredNorm, map_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [pderiv_X_of_ne hji]
  · simp

/-- Twice differentiating `|x|² * p` in the coordinate `i` gives
`2 p + 4 Xᵢ ∂ᵢ p + |x|² ∂ᵢ² p`. -/
lemma pderiv_twice_polynomialSquaredNorm_mul {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) (i : Fin d) :
    pderiv i (pderiv i (polynomialSquaredNorm d * p)) =
      2 * p + 4 * (X i * pderiv i p) +
        polynomialSquaredNorm d * pderiv i (pderiv i p) := by
  rw [pderiv_mul, map_add, pderiv_mul, pderiv_mul,
    pderiv_polynomialSquaredNorm]
  have htwo : pderiv i (2 : MvPolynomial (Fin d) ℝ) = 0 := by
    simpa only [Nat.cast_ofNat] using (pderiv i).map_natCast 2
  rw [pderiv_mul, htwo, pderiv_X_self]
  ring

/-- Product rule for the formal Laplacian against the squared norm:
`Δ(|x|² * p) = 2d · p + 4 ∑ᵢ Xᵢ ∂ᵢ p + |x|² Δp`. The middle term is the Euler operator
`∑ᵢ Xᵢ ∂ᵢ` applied to `p`. -/
theorem polynomialLaplacian_squaredNorm_mul {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) :
    polynomialLaplacian (polynomialSquaredNorm d * p) =
      (2 * (d : ℝ)) • p + 4 * (∑ i, X i * pderiv i p) +
        polynomialSquaredNorm d * polynomialLaplacian p := by
  simp only [polynomialLaplacian, pderiv_twice_polynomialSquaredNorm_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_C_mul, map_mul, map_ofNat]
  norm_num
  ring

end LatticeProb

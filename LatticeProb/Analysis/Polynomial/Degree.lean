/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/PolynomialDegree.lean.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# Degree bounds for formal partial derivatives and quadratic multipliers

A formal partial derivative lowers a supplied positive degree bound by one. Consequently,
multiplying a polynomial of total degree at most `m` by a polynomial `A` of total degree at most
`2` and applying the formal Laplacian gives a polynomial of total degree at most `m`.
Hence `q ↦ Δ(A q)` restricts
to a linear endomorphism of the finite-dimensional space of polynomials of total degree at most `m`.
-/

open scoped BigOperators
open MvPolynomial

namespace LatticeProb

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
/-- A formal partial derivative lowers a supplied positive degree bound. -/
theorem totalDegree_pderiv_le {p : MvPolynomial σ ℝ} {m : ℕ}
    (hp : p.totalDegree ≤ m + 1) (i : σ) : (pderiv i p).totalDegree ≤ m := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro a ha
  have hc : (pderiv i p).coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_pderiv] at hc
  have hcoeff : p.coeff (a + Finsupp.single i 1) ≠ 0 :=
    left_ne_zero_of_mul hc
  have hdeg := (MvPolynomial.le_totalDegree
    (MvPolynomial.mem_support_iff.mpr hcoeff)).trans hp
  have hadd : (a + Finsupp.single i 1).sum (fun _ n => n) =
      a.sum (fun _ n => n) + 1 := by
    rw [Finsupp.sum_add_index' (h := fun (_ : σ) (n : ℕ) => n)
      (fun _ => rfl) (fun _ _ _ => rfl)]
    simp
  rw [hadd] at hdeg
  omega

omit [Fintype σ] in
/-- Two formal partial derivatives of `A * p` have total degree at most `m` when `A` has total
degree at most `2` and `p` has total degree at most `m`. -/
theorem totalDegree_pderiv_pderiv_mul_le {A p : MvPolynomial σ ℝ} {m : ℕ}
    (hA : A.totalDegree ≤ 2) (hp : p.totalDegree ≤ m) (i j : σ) :
    (pderiv i (pderiv j (A * p))).totalDegree ≤ m := by
  apply totalDegree_pderiv_le _ i
  apply totalDegree_pderiv_le _ j
  exact (MvPolynomial.totalDegree_mul A p).trans (by omega)

/-- The formal Laplacian `∑ᵢ ∂ᵢ ∂ᵢ` of `A * p` has total degree at most `m` when `A` has total
degree at most `2` and `p` has total degree at most `m`. -/
theorem totalDegree_laplacian_mul_le {A p : MvPolynomial σ ℝ} {m : ℕ}
    (hA : A.totalDegree ≤ 2) (hp : p.totalDegree ≤ m) :
    (∑ i : σ, pderiv i (pderiv i (A * p))).totalDegree ≤ m := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact totalDegree_pderiv_pderiv_mul_le hA hp i i

/-- The linear map `q ↦ Δ(A q)` on the polynomials of total degree at most `m`, where `Δ` is the
formal Laplacian `∑ᵢ ∂ᵢ ∂ᵢ` and `A` is a polynomial of total degree at most `2`. For example,
`A = R² − ∑ᵢ Xᵢ²` satisfies `hA` and gives the operator for the ball of radius `R` about the origin. -/
noncomputable def quadraticLaplacianOnDegree (A : MvPolynomial σ ℝ)
    (hA : A.totalDegree ≤ 2) (m : ℕ) :
    MvPolynomial.restrictTotalDegree σ ℝ m →ₗ[ℝ]
      MvPolynomial.restrictTotalDegree σ ℝ m where
  toFun p := ⟨∑ i : σ, pderiv i (pderiv i (A * p.val)),
    (MvPolynomial.mem_restrictTotalDegree σ _ _).mpr
      (totalDegree_laplacian_mul_le hA
        ((MvPolynomial.mem_restrictTotalDegree σ _ _).mp p.property))⟩
  map_add' p q := by
    apply Subtype.ext
    change (∑ i : σ, pderiv i (pderiv i (A * (p.val + q.val)))) = _
    simp only [mul_add, map_add, Finset.sum_add_distrib, Submodule.coe_add]
  map_smul' c p := by
    apply Subtype.ext
    change (∑ i : σ, pderiv i (pderiv i (A * (c • p.val)))) = _
    simp only [mul_smul_comm, Derivation.map_smul, Finset.smul_sum,
      Submodule.coe_smul, RingHom.id_apply]

/-- The underlying polynomial of `quadraticLaplacianOnDegree A hA m p` is `∑ᵢ ∂ᵢ ∂ᵢ (A * p)`. -/
@[simp] theorem quadraticLaplacianOnDegree_apply (A : MvPolynomial σ ℝ)
    (hA : A.totalDegree ≤ 2) (m : ℕ)
    (p : MvPolynomial.restrictTotalDegree σ ℝ m) :
    (quadraticLaplacianOnDegree A hA m p).val =
      ∑ i : σ, pderiv i (pderiv i (A * p.val)) := rfl

end LatticeProb

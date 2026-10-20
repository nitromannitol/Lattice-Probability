/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/PolynomialAnalyticLaplacian.lean.
-/
import LatticeProb.Analysis.HarmonicBridge
import LatticeProb.Analysis.Polynomial.Laplacian
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Polynomial evaluations are smooth and their analytic Laplacian is the formal Laplacian

For a real polynomial `p` in `d` variables, `polynomialEval p` is its evaluation map on
`EuclideanSpace ℝ (Fin d)`. The file shows that this map is smooth, that its directional derivatives
along the standard orthonormal basis are the evaluations of the formal partial derivatives, and that
its analytic Laplacian is the evaluation of the formal Laplacian `polynomialLaplacian`. Consequently
a polynomial with zero formal Laplacian is harmonic on every set, in the sense of `IsHarmonicOn`.
-/

open MvPolynomial InnerProductSpace Laplacian
namespace LatticeProb

/-- Evaluation of a real polynomial in `d` variables at a point of `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ := MvPolynomial.eval (fun i ↦ x i) p

/-- The evaluation of a real polynomial is `C^n` for every `n`. -/
lemma contDiff_polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (polynomialEval p) := by
  have ha : AnalyticOnNhd ℝ (polynomialEval p) Set.univ :=
    AnalyticOnNhd.eval_continuousLinearMap' (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) (B := ℝ)
      (fun i : Fin d ↦ PiLp.proj 2 (fun _ : Fin d ↦ ℝ) i) p
  exact ha.contDiff (n := n)

/-- The evaluation of a real polynomial is differentiable. -/
lemma differentiable_polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    Differentiable ℝ (polynomialEval p) :=
  (contDiff_polynomialEval p (n := 1)).differentiable (by norm_num)

/-- Formal differentiation in one coordinate gives the directional derivative
along the corresponding vector of the Euclidean orthonormal basis. -/
theorem fderiv_polynomialEval_basis {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    fderiv ℝ (polynomialEval p) x (EuclideanSpace.basisFun (Fin d) ℝ i) =
      polynomialEval (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hconst : polynomialEval (C c : MvPolynomial (Fin d) ℝ) =
        fun _ : EuclideanSpace ℝ (Fin d) ↦ c := by
      funext y
      simp [polynomialEval]
    rw [hconst, fderiv_const_apply]
    simp [polynomialEval]
  | add p q hp hq =>
    have hadd : polynomialEval (p + q) = fun y ↦ polynomialEval p y + polynomialEval q y := by
      funext y
      simp [polynomialEval]
    rw [hadd, fderiv_fun_add (differentiable_polynomialEval p x)
      (differentiable_polynomialEval q x), add_apply, hp, hq]
    simp [polynomialEval, map_add]
  | mul_X p j hp =>
    have hmul : polynomialEval (p * X j) = fun y ↦ polynomialEval p y * y j := by
      funext y
      simp [polynomialEval]
    have hcoord : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin d) ↦ y j) x =
        PiLp.proj 2 (fun _ : Fin d ↦ ℝ) j :=
      (PiLp.proj 2 (fun _ : Fin d ↦ ℝ) j).fderiv
    have hdcoord : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin d) ↦ y j) x :=
      (PiLp.proj 2 (fun _ : Fin d ↦ ℝ) j).differentiableAt
    rw [hmul, fderiv_fun_mul (differentiable_polynomialEval p x) hdcoord]
    simp only [add_apply, smul_apply, smul_eq_mul, hcoord, hp]
    by_cases hij : i = j
    · subst j
      simp [polynomialEval, EuclideanSpace.basisFun_apply, PiLp.proj_apply, mul_comm]
    · simp [polynomialEval, EuclideanSpace.basisFun_apply, PiLp.proj_apply, Ne.symm hij, mul_comm]

/-- Repeating the directional derivative along the Euclidean orthonormal basis yields the
evaluation of the second formal partial derivative. -/
theorem fderiv_twice_polynomialEval_basis {d : ℕ} (p : MvPolynomial (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i j : Fin d) :
    fderiv ℝ (fderiv ℝ (polynomialEval p)) x
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ j) =
        polynomialEval (pderiv i (pderiv j p)) x := by
  have heq : (fun y ↦ fderiv ℝ (polynomialEval p) y
      (EuclideanSpace.basisFun (Fin d) ℝ j)) = polynomialEval (pderiv j p) :=
    funext (fun y ↦ fderiv_polynomialEval_basis p y j)
  have hDf : Differentiable ℝ (fderiv ℝ (polynomialEval p)) :=
    ((contDiff_polynomialEval p (n := 2)).fderiv_right (by norm_num) :
      ContDiff ℝ 1 (fderiv ℝ (polynomialEval p))).differentiable (by norm_num)
  have h := fderiv_polynomialEval_basis (pderiv j p) x i
  rw [← heq, fderiv_clm_apply (hDf x) (differentiableAt_const _)] at h
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using h

/-- The analytic Laplacian of the evaluation of `p` is the evaluation of the formal Laplacian
`polynomialLaplacian p`, in every finite Euclidean dimension. -/
theorem laplacian_polynomialEval {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    Δ (polynomialEval p) = polynomialEval (polynomialLaplacian p) := by
  funext x
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (polynomialEval p)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  change (∑ i, iteratedFDeriv ℝ 2 (polynomialEval p) x
    ![EuclideanSpace.basisFun (Fin d) ℝ i, EuclideanSpace.basisFun (Fin d) ℝ i]) = _
  simp only [polynomialEval, polynomialLaplacian, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact fderiv_twice_polynomialEval_basis p x i i

/-- A real polynomial with zero formal Laplacian is harmonic on every subset `U` of
`EuclideanSpace ℝ (Fin d)`. -/
lemma isHarmonicOn_polynomialEval_of_laplacian_eq_zero {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) (hp : polynomialLaplacian p = 0)
    (U : Set (EuclideanSpace ℝ (Fin d))) :
    IsHarmonicOn (polynomialEval p) U := by
  refine ⟨(contDiff_polynomialEval p).contDiffOn, fun x hx ↦ ?_⟩
  rw [laplacian_polynomialEval, hp]
  simp [polynomialEval]

namespace PolynomialAnalyticExample

/-- The polynomial `x₀ x₁` has zero formal Laplacian, so its evaluation is harmonic on all of
`EuclideanSpace ℝ (Fin 2)`: the hypothesis of `isHarmonicOn_polynomialEval_of_laplacian_eq_zero`
holds for a polynomial of degree two. -/
theorem isHarmonicOn_X0_mul_X1_univ :
    IsHarmonicOn (polynomialEval (X 0 * X 1 : MvPolynomial (Fin 2) ℝ)) Set.univ :=
  isHarmonicOn_polynomialEval_of_laplacian_eq_zero _ (by
    simp [polynomialLaplacian, Fin.sum_univ_two]) _

end PolynomialAnalyticExample

end LatticeProb

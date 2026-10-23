import LatticeProb.Analysis.Elliptic.Domain

/-!
# Classical Dirichlet solutions and coordinate differentiation

The classical carrier records interior twice continuous differentiability, continuity up to
the boundary, zero boundary data, and the pointwise elliptic equation. Coordinate calculations
fix the normalization of the Laplacian on quadratic polynomials.
-/

namespace LatticeProb.Elliptic

open LatticeProb.Euclidean.Lattice
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- `u` is a classical solution of `μ u − a₀ Δ u = f` in `U`, `u = 0` on `∂U`. -/
def IsClassicalDirichletSolution (U : Set (Fin d → ℝ)) (μ a₀ : ℝ)
    (f u : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 u U ∧ ContinuousOn u (closure U) ∧
    (∀ x ∈ frontier U, u x = 0) ∧
    ∀ x ∈ U, μ * u x - a₀ * laplacian u x = f x

/-- Twice continuous differentiability makes the second coordinate derivatives commute. -/
theorem secondPartial_comm {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (i j : Fin d) :
    secondPartial i j f x = secondPartial j i f x := by
  exact IsSymmSndFDerivAt.iteratedFDeriv_cons
    (hf := hf.isSymmSndFDerivAt (by norm_num))

/-- The derivative of an affine function of the squared Euclidean radius. -/
theorem fderiv_affine_sum_sq (c b : ℝ) (x : Fin d → ℝ) :
    fderiv ℝ (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) x =
      b • ∑ k, (2 * x k) • ContinuousLinearMap.proj k := by
  rw [fderiv_const_add]
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun k (_ : k ∈ Finset.univ) => (hasFDerivAt_apply (𝕜 := ℝ) k x).pow 2)
  convert (hsum.const_mul b).fderiv using 1
  · simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, nsmul_eq_mul]

/-- The coordinate derivative of an affine function of the squared Euclidean radius. -/
theorem partialDeriv_affine_sum_sq (c b : ℝ) (i : Fin d) (x : Fin d → ℝ) :
    partialDeriv i (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) x =
      2 * b * x i := by
  rw [partialDeriv, fderiv_affine_sum_sq]
  simp [Pi.single_apply, mul_comm, mul_left_comm]

/-- Evaluating the Hessian in two coordinate directions differentiates a first partial. -/
theorem secondPartial_eq_fderiv_partialDeriv {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (i j : Fin d) (x : Fin d → ℝ) :
    secondPartial i j f x = fderiv ℝ (partialDeriv j f) x (Pi.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  simp only [secondPartial, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  change ((fderiv ℝ (fderiv ℝ f) x) (Pi.single i 1)) (Pi.single j 1) =
    (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j 1)) x) (Pi.single i 1)
  rw [fderiv_clm_apply hd (differentiableAt_const (Pi.single j 1))]
  simp

/-- The Hessian of an affine function of the squared radius is twice its scalar coefficient. -/
theorem secondPartial_affine_sum_sq (c b : ℝ) (i j : Fin d) (x : Fin d → ℝ) :
    secondPartial i j (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) x =
      if i = j then 2 * b else 0 := by
  have hf : ContDiff ℝ 2 (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) := by
    fun_prop
  rw [secondPartial_eq_fderiv_partialDeriv hf]
  have hp : partialDeriv j (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) =
      fun y => 2 * b * y j := funext (partialDeriv_affine_sum_sq c b j)
  rw [hp, ((hasFDerivAt_apply (𝕜 := ℝ) j x).const_mul (2 * b)).fderiv]
  simp [Pi.single_apply, eq_comm]

/-- The Laplacian of an affine function of squared radius is `2 b d`. -/
theorem laplacian_affine_sum_sq (c b : ℝ) (x : Fin d → ℝ) :
    laplacian (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) x = 2 * b * d := by
  simp only [laplacian, secondPartial_affine_sum_sq, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The Laplacian of squared Euclidean radius is twice the dimension. -/
theorem laplacian_sum_sq (x : Fin d → ℝ) :
    laplacian (fun y : Fin d → ℝ => ∑ k, y k ^ 2) x = 2 * d := by
  simpa only [zero_add, one_mul, mul_one] using laplacian_affine_sum_sq 0 1 x

end

end LatticeProb.Elliptic

/-
# The Gaussian density and its covariance-coordinate derivatives

Normal-comparison route items 3 and 4 (`scratch/pk/normalcompare-route.md`).
`LatticeProb.multivariateGaussian_eq_withDensity` gives the density of `N(0, S)` on
`EuclideanSpace ℝ (Fin n)` for positive definite `S`.  The differentiation and boundary-integral
steps of the route are cleanest on plain functions `Fin n → ℝ`, where `Function.update` is
available, so this file names that density once,

  `covDensity S x = (2π)^{-n/2} (det S)^{-1/2} exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)`,

proves it positive, restates the density in terms of it, and computes its first and second
coordinate partials along a line: with `a x = S⁻¹ *ᵥ x`,

  `∂_i p = -(a x)_i p`,    `∂_j ∂_i p = ((a x)_i (a x)_j - S⁻¹ i j) p`.

These are the density inputs the orthant integration by parts consumes.  No `External` is
touched and no `Prop` is frozen.
-/
import LatticeProb.Prob.NormalComparisonDensity

open Filter Topology Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-! ### The density as a function on `Fin n → ℝ` -/

/-- The density of the centred Gaussian `N(0, S)` as a function on `Fin n → ℝ`:
`(2π)^{-n/2} (det S)^{-1/2} exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)`. -/
noncomputable def covDensity {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
    Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x)) / 2)

/-- The density of a positive definite Gaussian is strictly positive. -/
theorem covDensity_pos {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (x : Fin n → ℝ) : 0 < covDensity S x := by
  unfold covDensity
  have h2pi : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos h2pi _) (Real.rpow_pos_of_pos hS.det_pos _))
    (Real.exp_pos _)

/-- `LatticeProb.multivariateGaussian_eq_withDensity` in terms of `covDensity`. -/
theorem multivariateGaussian_eq_withDensity_covDensity {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
      = (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (fun y => ENNReal.ofReal (covDensity S (WithLp.ofLp y))) :=
  multivariateGaussian_eq_withDensity S hS

/-! ### Algebra along a coordinate line -/

/-- The point `update x j s` is `update x j 0 + s • e_j`. -/
private lemma update_eq_add_smul_single {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    Function.update x j s = Function.update x j 0 + s • (Pi.single j 1 : Fin n → ℝ) := by
  funext k
  by_cases hk : k = j
  · subst hk; simp
  · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]

/-- The inverse of a positive definite real matrix is symmetric (entrywise). -/
private lemma inv_apply_comm {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (i j : Fin n) : S⁻¹ i j = S⁻¹ j i := by
  have h := hS.isHermitian.inv.apply i j
  simpa using h.symm

/-- Coordinates of `T *ᵥ update x j s`: affine in `s` with slope `T i j`. -/
private lemma mulVec_update_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (i j : Fin n) (s : ℝ) :
    (T *ᵥ Function.update x j s) i = (T *ᵥ Function.update x j 0) i + s * T i j := by
  rw [update_eq_add_smul_single x j s, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

/-- The quadratic form of a symmetric matrix along a coordinate line. -/
private lemma quad_update {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i j, T i j = T j i)
    (x : Fin n → ℝ) (j : Fin n) (s : ℝ) :
    Function.update x j s ⬝ᵥ (T *ᵥ Function.update x j s)
      = T j j * s ^ 2 + 2 * (T *ᵥ Function.update x j 0) j * s
          + Function.update x j 0 ⬝ᵥ (T *ᵥ Function.update x j 0) := by
  set y0 := Function.update x j 0 with hy0
  have hdot : y0 ⬝ᵥ (T *ᵥ (Pi.single j 1 : Fin n → ℝ)) = (T *ᵥ y0) j := by
    rw [Matrix.mulVec_single_one]
    simp only [dotProduct, Matrix.mulVec, Matrix.col_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hT k j, mul_comm]
  rw [update_eq_add_smul_single x j s, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_dotProduct,
    dotProduct_smul, hdot, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]
  ring

/-! ### The density and its coordinate partials along a line -/

/-- Along a coordinate line the density is a constant times `exp (a s² + b s)` with
`a = -(S⁻¹ j j / 2) < 0` and `b = -(S⁻¹ *ᵥ update x j 0) j`. -/
private lemma covDensity_update_eq {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (x : Fin n → ℝ) (j : Fin n) :
    ∃ K : ℝ, ∀ s : ℝ, covDensity S (Function.update x j s)
      = K * Real.exp (-(S⁻¹ j j / 2) * s ^ 2 + (-((S⁻¹ *ᵥ Function.update x j 0) j)) * s) := by
  refine ⟨(2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
    Real.exp (-(Function.update x j 0 ⬝ᵥ (S⁻¹ *ᵥ Function.update x j 0)) / 2), fun s => ?_⟩
  have key : ∀ α m γ s : ℝ, Real.exp (-(α * s ^ 2 + 2 * m * s + γ) / 2)
      = Real.exp (-γ / 2) * Real.exp (-(α / 2) * s ^ 2 + (-m) * s) := by
    intro α m γ s
    rw [← Real.exp_add]
    congr 1
    ring
  unfold covDensity
  rw [quad_update S⁻¹ (inv_apply_comm hS) x j s, key]
  ring

/-- `a = -(S⁻¹ j j / 2)` is negative. -/
private lemma neg_inv_diag_div_two_lt {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (j : Fin n) : -(S⁻¹ j j / 2) < 0 := by
  have := hS.inv.diag_pos (i := j)
  linarith

/-- `∂_i p = -(S⁻¹ x)_i p` along the line through `x` in direction `e_i`. -/
theorem hasDerivAt_covDensity_update {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s => covDensity S (Function.update x i s))
      (-((S⁻¹ *ᵥ Function.update x i t) i) * covDensity S (Function.update x i t)) t := by
  obtain ⟨K, hK⟩ := covDensity_update_eq hS x i
  have hfun : (fun s => covDensity S (Function.update x i s))
      = fun s => K * Real.exp (-(S⁻¹ i i / 2) * s ^ 2
          + (-((S⁻¹ *ᵥ Function.update x i 0) i)) * s) := funext hK
  rw [hfun, hK t, mulVec_update_apply S⁻¹ x i i t]
  have hq : HasDerivAt (fun s : ℝ => -(S⁻¹ i i / 2) * s ^ 2
      + (-((S⁻¹ *ᵥ Function.update x i 0) i)) * s)
      (-(S⁻¹ i i / 2) * ((2 : ℕ) * t ^ (2 - 1)) + (-((S⁻¹ *ᵥ Function.update x i 0) i)) * 1) t :=
    ((hasDerivAt_pow 2 t).const_mul _).add ((hasDerivAt_id' t).const_mul _)
  refine (hq.exp.const_mul K).congr_deriv ?_
  push_cast
  ring

/-- The second derivative: `∂_j(-(S⁻¹ x)_i p) = ((S⁻¹ x)_i (S⁻¹ x)_j - S⁻¹ i j) p`. -/
theorem hasDerivAt_covDensity_partial_update {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) (x : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    HasDerivAt
      (fun s => -((S⁻¹ *ᵥ Function.update x j s) i) * covDensity S (Function.update x j s))
      ((((S⁻¹ *ᵥ Function.update x j t) i) * ((S⁻¹ *ᵥ Function.update x j t) j) - S⁻¹ i j)
        * covDensity S (Function.update x j t)) t := by
  have h1 : HasDerivAt (fun s => -((S⁻¹ *ᵥ Function.update x j s) i)) (-S⁻¹ i j) t := by
    have hfun : (fun s : ℝ => -((S⁻¹ *ᵥ Function.update x j s) i))
        = fun s => -((S⁻¹ *ᵥ Function.update x j 0) i + s * S⁻¹ i j) := by
      funext s
      rw [mulVec_update_apply]
    rw [hfun]
    exact ((((hasDerivAt_id' t).mul_const (S⁻¹ i j)).const_add _).neg).congr_deriv (by simp)
  refine (h1.mul (hasDerivAt_covDensity_update hS x j t)).congr_deriv ?_
  ring

end LatticeProb

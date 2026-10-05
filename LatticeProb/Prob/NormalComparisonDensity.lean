/-
# The multivariate Gaussian density: the covariance density assembly step

Route: `scratch/pk/normalcompare-route.md`, item 1 — the base case behind
`Sandpile.External.NormalComparison` (Li--Shao Corollary 2.1).

`LatticeProb/Gauss/MultivariateDensity.lean` lands the Cramer--Wold representation
`N(0,S) = (standard Gaussian).map (√S ·)` and the determinant factor `det (√S) = (det S)^{1/2}`.
This file lands the density itself for a positive definite covariance `S`,

  `N(0,S) = volume.withDensity (ofReal ((2π)^{-n/2} (det S)^{-1/2}
    exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)))`,

by the change of variables `∫ f d(N(0,S)) = ∫ f (√S x) dγ` along the invertible `√S`, using
`LatticeProb.map_withDensity_linearEquiv_apply` and
`LatticeProb.stdGaussian_euclidean_eq_withDensity`, the determinant factor, and the quadratic form
of the inverse root.

No `External` is touched and no `Prop` is frozen.
-/
import LatticeProb.Gauss.MultivariateDensity
import LatticeProb.Prob.GaussOrthant

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal MatrixOrder

namespace LatticeProb

/-- **The quadratic form of the inverse square root.**  For positive definite `S`, the quadratic
form of `(√S)⁻¹` is that of `S⁻¹`: `‖(√S)⁻¹ y‖² = y ⬝ᵥ (S⁻¹ *ᵥ y)`.  The proof uses the
symmetry of `CFC.sqrt S` (unpackaged in this Mathlib revision, recovered from
`CFC.sqrt_nonneg … .isSelfAdjoint.isHermitian`) and `(√S)⁻¹ * (√S)⁻¹ = (√S * √S)⁻¹ = S⁻¹`. -/
private theorem norm_sq_toEuclideanCLM_inv_sqrt {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosDef) (y : EuclideanSpace ℝ (Fin n)) :
    ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y‖ ^ 2 = y ⬝ᵥ S⁻¹ *ᵥ y := by
  have hsym : ((CFC.sqrt S)⁻¹)ᵀ = (CFC.sqrt S)⁻¹ := by
    have hher : (CFC.sqrt S).IsHermitian := (CFC.sqrt_nonneg S).isSelfAdjoint.isHermitian
    have hMt : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
      ext i j
      have h := congr_fun (congr_fun hher i) j
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using h
    rw [transpose_nonsing_inv, hMt]
  have hmm : (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ = S⁻¹ := by
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]
  have hMM : ((CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹)ᵀ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ := by
    rw [transpose_mul, hsym]
  have hvm : y.ofLp ᵥ* ((CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹)
      = ((CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹) *ᵥ y.ofLp := by
    conv_lhs => rw [show (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹
      = (((CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹)ᵀ)ᵀ from (transpose_transpose _).symm]
    rw [vecMul_transpose (((CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹)ᵀ) y.ofLp, hMM]
  have hinner : inner ℝ (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y)
        (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y)
      = ((CFC.sqrt S)⁻¹ *ᵥ y.ofLp) ⬝ᵥ ((CFC.sqrt S)⁻¹ *ᵥ y.ofLp) := by
    have h1 : inner ℝ (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y)
          (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y)
        = (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y).ofLp ⬝ᵥ
            (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y).ofLp := by
      rw [PiLp.inner_apply]
      simp only [RCLike.inner_apply, conj_trivial, dotProduct]
    rw [h1, ofLp_toEuclideanCLM]
  rw [← real_inner_self_eq_norm_sq, hinner,
    dotProduct_mulVec, vecMul_mulVec, hsym, hvm, dotProduct_comm, hmm]

/-- **The density of the correlated multivariate Gaussian.**  For a positive definite
`S : Matrix (Fin n) (Fin n) ℝ`,

`N(0, S) = volume.withDensity (fun x => ofReal ((2π)^{-n/2} (det S)^{-1/2}
  * exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)))`.

This is route item 1: the change of variables `∫ f d(N(0,S)) = ∫ f (√S x) dγ` along the
invertible `√S`, using `LatticeProb.map_withDensity_linearEquiv_apply` and
`LatticeProb.stdGaussian_euclidean_eq_withDensity`, the determinant factor
`LatticeProb.det_sqrt_mul_self`, and the quadratic form of the inverse root. -/
theorem multivariateGaussian_eq_withDensity {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S
      = (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (fun x => ENNReal.ofReal
          ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
            Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x)) / 2))) := by
  classical
  have hMdet2 : (CFC.sqrt S).det * (CFC.sqrt S).det = S.det :=
    det_sqrt_mul_self (S := S) hS.posSemidef
  have hMdet_eq : (CFC.sqrt S).det = Real.sqrt S.det := by
    have h := Matrix.PosSemidef.det_sqrt (A := S) hS.posSemidef
    simpa using h
  have hMdet_pos : 0 < (CFC.sqrt S).det := by
    rw [hMdet_eq]; exact Real.sqrt_pos.mpr hS.det_pos
  have hMun : IsUnit (CFC.sqrt S).det := isUnit_iff_ne_zero.mpr hMdet_pos.ne'
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (CFC.sqrt S) hMun
  have he : ∀ x, e x = toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := by intro x; rfl
  have hesymm : ∀ y, e.symm y = toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y := by intro y; rfl
  have hedet : LinearMap.det (e : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
      = (CFC.sqrt S).det := LinearMap.det_toLin _ (CFC.sqrt S)
  have hAsymm : Measurable (e.symm :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
    have : Continuous (e.symm :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
      LinearMap.continuous_of_finiteDimensional _
    exact this.measurable
  have hg : Measurable fun y : EuclideanSpace ℝ (Fin n) => ∏ i, gaussianPDF 0 1 (y i) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF 0 1).comp (by fun_prop)
  have hSdet : (S.det : ℝ) ^ (-(1 : ℝ) / 2) = ((CFC.sqrt S).det)⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = (-1) / 2 by norm_num,
      Real.rpow_div_two_eq_sqrt (-1) hS.det_pos.le, Real.rpow_neg_one, ← hMdet_eq]
  have h2pi : (Real.sqrt (2 * Real.pi))⁻¹ ^ n
      = (2 * Real.pi) ^ (-(n : ℝ) / 2) := by
    have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hpos.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal |(LinearMap.det (e :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))⁻¹|
          * (∏ i, gaussianPDF 0 1 ((e.symm y) i))
        = ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) * (S.det) ^ (-(1 : ℝ) / 2) *
            Real.exp (-(y ⬝ᵥ (S⁻¹ *ᵥ y)) / 2)) := by
    intro y
    have hgz : (∏ i, gaussianPDF 0 1 ((e.symm y) i))
        = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ n *
            Real.exp (-(y ⬝ᵥ S⁻¹ *ᵥ y) / 2)) := by
      rw [prod_gaussianPDF]
      rw [hesymm, euclidean_sum_sq, norm_sq_toEuclideanCLM_inv_sqrt hS]
      simp only [mul_one, Fintype.card_fin, NNReal.coe_one]
    rw [hgz, ← ENNReal.ofReal_mul (abs_nonneg _), hedet,
      abs_of_pos (inv_pos.mpr hMdet_pos), hSdet, h2pi]
    congr 1
    ring
  have hemap : (stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (fun x => toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)
      = (stdGaussian (EuclideanSpace ℝ (Fin n))).map e := rfl
  rw [multivariateGaussian_eq_map, hemap, stdGaussian_euclidean_eq_withDensity]
  ext T hT
  rw [map_withDensity_linearEquiv_apply e hg hT, withDensity_apply _ hT]
  rw [show ENNReal.ofReal |(LinearMap.det (e :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))⁻¹|
        * ∫⁻ y in T, (∏ i, gaussianPDF 0 1 ((e.symm y) i))
      = ∫⁻ y in T, ENNReal.ofReal |(LinearMap.det (e :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))⁻¹|
        * (∏ i, gaussianPDF 0 1 ((e.symm y) i)) from
    (lintegral_const_mul _ (hg.comp hAsymm)).symm]
  apply lintegral_congr_ae
  filter_upwards with y
  exact hpoint y

end LatticeProb

/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.Gaussian.Basic at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Gaussian
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Finite Gaussian families: Gram bridge, Gram representation, integrability

We discharge the blueprint obligations `Blueprint.GramBridge`, `Blueprint.GramRepresentation`
and `Blueprint.MaxIntegrable`.

* `gramMap F v : E →L[ℝ] EuclideanSpace ℝ F` is the map `x ↦ (⟪v i, x⟫)_{i ∈ F}`.
* `map_gramMap_stdGaussian`: the image of `stdGaussian E` under `gramMap F v` is the
  multivariate Gaussian with the Gram matrix `(⟪v i, v j⟫)_{i,j ∈ F}` as covariance.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real WithLp
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace LQGDimension

section GramMap

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The continuous linear map `x ↦ (⟪v i, x⟫)_{i ∈ F}` from `E` to `EuclideanSpace ℝ F`. -/
def gramMap (F : Finset ι) (v : ι → E) : E →L[ℝ] EuclideanSpace ℝ F :=
  (EuclideanSpace.equiv F ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : F => innerSL ℝ (v i))

@[simp]
lemma gramMap_apply (F : Finset ι) (v : ι → E) (x : E) (i : F) :
    gramMap F v x i = ⟪v i, x⟫ := by
  simp [gramMap]

/-- The Gram matrix of a family of vectors is positive semidefinite. -/
lemma posSemidef_gramOn (F : Finset ι) (v : ι → E) :
    (Matrix.of fun i j : F => ⟪v i, v j⟫).PosSemidef :=
  Matrix.posSemidef_gram ℝ (fun i : F => v i)

variable [FiniteDimensional ℝ E]

lemma gramMap_adjoint_apply (F : Finset ι) (v : ι → E) (u : EuclideanSpace ℝ F) :
    (gramMap F v).adjoint u = ∑ i : F, u i • v i := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, sum_inner]
  simp [PiLp.inner_apply, inner_smul_left, real_inner_comm, mul_comm]

variable [MeasurableSpace E] [BorelSpace E]

/-- The law of `(⟪v i, x⟫)_{i ∈ F}` under `x ∼ stdGaussian E` is the centered multivariate
Gaussian with the Gram covariance matrix. -/
theorem map_gramMap_stdGaussian (F : Finset ι) (v : ι → E) [DecidableEq F] :
    (stdGaussian E).map (gramMap F v) =
      multivariateGaussian 0 (Matrix.of fun i j : F => ⟪v i, v j⟫) := by
  apply IsGaussian.ext
  · rw [integral_id_multivariateGaussian']
    simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id, integral_id_stdGaussian,
      map_zero]
  · ext u w
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian (posSemidef_gramOn F v), innerSL_apply_apply,
      gramMap_adjoint_apply, gramMap_adjoint_apply]
    have := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) (fun i : F => v i) (ofLp u) (ofLp w)
    rw [star_trivial] at this
    exact this.symm

end GramMap

/-! ### General (universe-polymorphic) versions -/

section General

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The expected maximum for the multivariate Gaussian with a Gram covariance equals the
expected maximum of the inner products with a standard Gaussian vector. -/
theorem gaussianExpectedMax_gram_eq_vecExpectedMax (F : Finset ι) (v : ι → E) (b : ι → ℝ) :
    gaussianExpectedMax F (fun i j => ⟪v i, v j⟫) b = vecExpectedMax F v b := by
  classical
  unfold gaussianExpectedMax vecExpectedMax
  beta_reduce
  rw [← map_gramMap_stdGaussian F v, integral_map (gramMap F v).continuous.aemeasurable]
  · simp only [gramMap_apply]
  · exact (Measurable.iSup fun i => by fun_prop).aestronglyMeasurable

/-- A kernel which is positive semidefinite on `F` is a Gram kernel on `F`, realised by the
columns of the matrix square root. -/
theorem exists_gram_of_psdOn (F : Finset ι) (C : ι → ι → ℝ) (hC : PSDOn F C) :
    ∃ v : ι → EuclideanSpace ℝ F, ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = C i j := by
  classical
  set S : Matrix F F ℝ := Matrix.of fun i j : F => C i j with hSdef
  set R : Matrix F F ℝ := CFC.sqrt S with hRdef
  have hRsa : Rᴴ = R := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRR : Rᴴ * R = S := by rw [hRsa]; exact CFC.sqrt_mul_sqrt_self S hC.nonneg
  refine ⟨fun i => if h : i ∈ F then toLp 2 (fun k => R k ⟨i, h⟩) else 0, ?_⟩
  intro i hi j hj
  have hij := congrFun (congrFun hRR ⟨i, hi⟩) ⟨j, hj⟩
  simp only [hi, hj, dite_true]
  rw [PiLp.inner_apply]
  simpa [S, Matrix.mul_apply, mul_comm] using hij

/-- A finite maximum of affine functions of a standard Gaussian vector is integrable. -/
theorem integrable_iSup_inner_add (F : Finset ι) (v : ι → E) (b : ι → ℝ) :
    Integrable (fun x => ⨆ i : F, ⟪v i, x⟫ + b i) (stdGaussian E) := by
  have hint : ∀ i : F, Integrable (fun x : E => ⟪v i, x⟫ + b i) (stdGaussian E) := fun i =>
    (IsGaussian.integrable_id.const_inner (v i)).add (integrable_const _)
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ => (hint i).abs) ?_ ?_
  · exact (Measurable.iSup fun i => by fun_prop).aestronglyMeasurable
  · filter_upwards with x
    rcases isEmpty_or_nonempty F with h | h
    · simp
    · obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i : F => ⟪v i, x⟫ + b i)
      rw [← hj, Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i : F => |⟪v i, x⟫ + b i|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ j)

end General

/-! ### Corollaries -/

/-- `gaussianExpectedMax F C b` only depends on the values of `C` on `F × F`. -/
theorem gaussianExpectedMax_congr {ι : Type*} (F : Finset ι) {C C' : ι → ι → ℝ} (b : ι → ℝ)
    (h : ∀ i ∈ F, ∀ j ∈ F, C i j = C' i j) :
    gaussianExpectedMax F C b = gaussianExpectedMax F C' b := by
  have hM : (Matrix.of fun i j : F => C i j) = Matrix.of fun i j : F => C' i j := by
    ext i j
    simp [h i i.2 j j.2]
  unfold gaussianExpectedMax
  rw [hM]

/-- The expected maximum `vecExpectedMax F v b` only depends on the Gram matrix of `v` on `F`
(the two families may live in different spaces). -/
theorem vecExpectedMax_eq_of_gram_eq {ι E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E']
    (F : Finset ι) (v : ι → E) (w : ι → E') (b : ι → ℝ)
    (h : ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = ⟪w i, w j⟫) :
    vecExpectedMax F v b = vecExpectedMax F w b := by
  rw [← gaussianExpectedMax_gram_eq_vecExpectedMax, ← gaussianExpectedMax_gram_eq_vecExpectedMax]
  exact gaussianExpectedMax_congr F b h

/-- For a kernel `C` which is positive semidefinite on `F`, the Gaussian expected maximum is
realised as `vecExpectedMax` for some family of vectors with Gram matrix `C` on `F`. -/
theorem exists_vecExpectedMax_eq_gaussianExpectedMax {ι : Type*} (F : Finset ι)
    (C : ι → ι → ℝ) (hC : PSDOn F C) :
    ∃ v : ι → EuclideanSpace ℝ F, (∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = C i j) ∧
      ∀ b : ι → ℝ, gaussianExpectedMax F C b = vecExpectedMax F v b := by
  obtain ⟨v, hv⟩ := exists_gram_of_psdOn F C hC
  refine ⟨v, hv, fun b => ?_⟩
  rw [← gaussianExpectedMax_gram_eq_vecExpectedMax]
  exact gaussianExpectedMax_congr F b fun i hi j hj => (hv i hi j hj).symm

/-! ### The three blueprint obligations -/

/-- **Gram bridge** (blueprint obligation). -/
theorem gramBridge : Blueprint.GramBridge := by
  intro ι E _ _ _ _ _ F v b
  exact gaussianExpectedMax_gram_eq_vecExpectedMax F v b

/-- **Gram representation** (blueprint obligation). -/
theorem gramRepresentation : Blueprint.GramRepresentation := by
  intro ι F C hC
  exact exists_gram_of_psdOn F C hC

/-- **Integrability of the maximum** (blueprint obligation). -/
theorem maxIntegrable : Blueprint.MaxIntegrable := by
  intro ι E _ _ _ _ _ F v b
  exact integrable_iSup_inner_add F v b

end LQGDimension

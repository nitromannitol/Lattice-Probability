/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Gaussian/PittVector.lean.
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Pi
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance

/-!
# Gram representation of a Gaussian vector

For a random vector `X : Ω → (ι → ℝ)` with `ι` finite and Gaussian law (any mean and any,
possibly degenerate, covariance), the law of `X` is the law of an affine image
`m + (⟪v i, x⟫)ᵢ` of a standard Gaussian vector `x` in a Euclidean space, where `m` is the mean
of `X` and the vectors `v i` satisfy `⟪v i, v j⟫ = cov(X i, X j)` (`LatticeProb.Pitt.exists_gram_map_eq`).

The file also proves the auxiliary facts this representation rests on: the unit vectors of
`ι → ℝ`, the linear map `x ↦ (⟪v i, x⟫)ᵢ` (`LatticeProb.Pitt.gramCLM`) and its composition with
continuous linear functionals, the square integrability of the coordinates of a Gaussian vector,
and the variance of a linear combination of its coordinates.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Matrix MatrixOrder

namespace LatticeProb

namespace Pitt

variable {ι : Type*} [Fintype ι]

/-- The `i`-th unit vector of `ι → ℝ`. -/
def unitVec [DecidableEq ι] (i : ι) : ι → ℝ := fun j => if i = j then 1 else 0

omit [Fintype ι] in
/-- Every unit vector of `ι → ℝ` has nonnegative coordinates. -/
lemma unitVec_nonneg [DecidableEq ι] (i : ι) : 0 ≤ unitVec i := fun j => by
  unfold unitVec; split_ifs <;> norm_num

/-- Every unit vector of `ι → ℝ` has sup-norm at most one. -/
lemma norm_unitVec_le [DecidableEq ι] (i : ι) : ‖unitVec i‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
    unfold unitVec; split_ifs <;> simp

/-- A continuous linear functional on `ι → ℝ` is the sum of the coordinates of its argument
weighted by its values on the unit vectors. -/
lemma dual_apply_eq_sum [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (y : ι → ℝ) :
    L y = ∑ i, y i * L (unitVec i) := by
  have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) y
  exact this.trans (by simp only [smul_eq_mul]; rfl)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The map `x ↦ (⟪v i, x⟫)ᵢ` from a real inner product space to `ι → ℝ`. -/
def gramCLM (v : ι → E) : E →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun i => innerSL ℝ (v i)

omit [Fintype ι] in
/-- The `i`-th coordinate of `gramCLM v x` is the inner product `⟪v i, x⟫`. -/
@[simp] lemma gramCLM_apply (v : ι → E) (x : E) (i : ι) : gramCLM v x i = ⟪v i, x⟫ := by
  simp [gramCLM]

/-- Composing a continuous linear functional on `ι → ℝ` with `gramCLM v` gives the inner product
with the combination `∑ i, L (unitVec i) • v i`. -/
lemma dual_comp_gramCLM [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (v : ι → E) :
    L.comp (gramCLM v) = innerSL ℝ (∑ i, L (unitVec i) • v i) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, dual_apply_eq_sum L, innerSL_apply_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gramCLM_apply, real_inner_smul_left, mul_comm]

/-- The inner product of two linear combinations of vectors is the bilinear expansion in the
coefficients and the pairwise inner products. -/
lemma inner_sum_smul_sum_smul (a b : ι → ℝ) (v : ι → E) :
    ⟪∑ i, a i • v i, ∑ j, b j • v j⟫ = ∑ i, ∑ j, a i * b j * ⟪v i, v j⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Each coordinate of a Gaussian random vector is square integrable. -/
lemma memLp_coord {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P) (i : ι) :
    MemLp (fun ω => X ω i) 2 P :=
  (hX.map_fun (ContinuousLinearMap.proj i)).memLp_two

/-- The variance of a linear combination of the coordinates of a Gaussian random vector is the
quadratic form of its covariance matrix. -/
lemma variance_sum_coord {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P) (c : ι → ℝ) :
    Var[fun ω => ∑ i, c i * X ω i; P] =
      ∑ i, ∑ j, c i * c j * cov[fun ω => X ω i, fun ω => X ω j; P] := by
  have := hX.isProbabilityMeasure
  have hL : ∀ i, MemLp (fun ω => c i * X ω i) 2 P := fun i => (memLp_coord hX i).const_mul _
  have hm : AEMeasurable (fun ω => ∑ i, c i * X ω i) P :=
    (memLp_finsetSum _ fun i _ => hL i).aestronglyMeasurable.aemeasurable
  rw [← covariance_self hm, covariance_fun_sum_fun_sum hL hL]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Gram representation of a Gaussian vector.** A Gaussian random vector `X : Ω → (ι → ℝ)` has
the same law as the affine image `m + gramCLM v x` of a standard Gaussian vector `x` in
`EuclideanSpace ℝ ι`, where `m` is the mean of `X` and `⟪v i, v j⟫` is the covariance of
`X i` and `X j`. -/
theorem exists_gram_map_eq {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P) :
    ∃ v : ι → EuclideanSpace ℝ ι,
      (∀ i j, ⟪v i, v j⟫ = cov[fun ω => X ω i, fun ω => X ω j; P]) ∧
      P.map X = (stdGaussian (EuclideanSpace ℝ ι)).map
        (fun x => (fun i => ∫ ω, X ω i ∂P) + gramCLM v x) := by
  classical
  have := hX.isProbabilityMeasure
  set C : ι → ι → ℝ := fun i j => cov[fun ω => X ω i, fun ω => X ω j; P] with hC
  set S : Matrix ι ι ℝ := Matrix.of C with hS
  have hPSD : S.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun t => ?_
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [star_trivial, hS, Matrix.of_apply, hC]
      exact covariance_comm _ _
    · have : star t ⬝ᵥ S *ᵥ t = Var[fun ω => ∑ i, t i * X ω i; P] := by
        rw [variance_sum_coord hX t]
        simp only [star_trivial, dotProduct, Matrix.mulVec, hS, Matrix.of_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [this]; exact variance_nonneg _ _
  set R : Matrix ι ι ℝ := CFC.sqrt S with hRdef
  have hRsa : Rᴴ = R := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRR : Rᴴ * R = S := by rw [hRsa]; exact CFC.sqrt_mul_sqrt_self S hPSD.nonneg
  set v : ι → EuclideanSpace ℝ ι := fun i => WithLp.toLp 2 (fun k => R k i) with hv
  have hvv : ∀ i j, ⟪v i, v j⟫ = C i j := fun i j => by
    have hij := congrFun (congrFun hRR i) j
    rw [hv, PiLp.inner_apply]
    simpa [S, Matrix.mul_apply, mul_comm] using hij
  refine ⟨v, hvv, ?_⟩
  set γ := stdGaussian (EuclideanSpace ℝ ι)
  set m : ι → ℝ := fun i => ∫ ω, X ω i ∂P with hm
  set Y : EuclideanSpace ℝ ι → ι → ℝ := fun x => m + gramCLM v x with hY
  have hYmap : γ.map Y = (γ.map (gramCLM v)).map (fun y => m + y) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  have : IsGaussian (γ.map Y) := by rw [hYmap]; infer_instance
  have hYG : HasGaussianLaw Y γ := IsGaussian.hasGaussianLaw
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [hX.charFunDual_map_eq_fun, hYG.charFunDual_map_eq_fun]
  have hint : ∀ i, Integrable (fun ω => X ω i) P := fun i =>
    (memLp_coord hX i).integrable one_le_two
  have hLX : (fun ω => L (X ω)) = fun ω => ∑ i, L (unitVec i) * X ω i := by
    funext ω; rw [dual_apply_eq_sum L]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hLY : (fun x => L (Y x)) = fun x => L m + (innerSL ℝ (∑ i, L (unitVec i) • v i)) x := by
    funext x; rw [hY, map_add, ← dual_comp_gramCLM L v, ContinuousLinearMap.comp_apply]
  have hmean : ∫ ω, L (X ω) ∂P = ∫ x, L (Y x) ∂γ := by
    have h1 : ∫ ω, L (X ω) ∂P = ∑ i, L (unitVec i) * m i := by
      rw [hLX, integral_finsetSum _ fun i _ => (hint i).const_mul _]
      simp only [integral_const_mul, hm]
    have h2 : ∫ x, L (Y x) ∂γ = L m := by
      have hi : Integrable (fun x : EuclideanSpace ℝ ι => (innerSL ℝ (∑ i, L (unitVec i) • v i)) x)
          γ := (innerSL ℝ (∑ i, L (unitVec i) • v i)).integrable_comp IsGaussian.integrable_id
      rw [hLY, integral_add (integrable_const _) hi, integral_strongDual_stdGaussian]
      simp
    rw [h1, h2, dual_apply_eq_sum L m]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hvar : Var[fun ω => L (X ω); P] = Var[fun x => L (Y x); γ] := by
    rw [hLX, hLY, variance_sum_coord hX,
      variance_const_add (innerSL ℝ _).continuous.aestronglyMeasurable,
      variance_dual_stdGaussian, innerSL_apply_norm, ← real_inner_self_eq_norm_sq,
      inner_sum_smul_sum_smul]
    simp only [hvv, hC]
  rw [hmean, hvar]

namespace GramExample

-- The coordinates of a standard Gaussian vector in `EuclideanSpace ℝ ι` form a Gaussian random
-- vector, so the hypothesis `HasGaussianLaw X P` of `exists_gram_map_eq` is satisfiable.
example [DecidableEq ι] :
    HasGaussianLaw (fun x : EuclideanSpace ℝ ι =>
      gramCLM (fun i => EuclideanSpace.single i (1 : ℝ)) x) (stdGaussian (EuclideanSpace ℝ ι)) :=
  (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℝ ι))).map_fun _

end GramExample

end Pitt

end LatticeProb

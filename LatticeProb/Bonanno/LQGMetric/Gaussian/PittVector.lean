/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.PittVector at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.PittCore
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Moments.Covariance
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Pitt's inequality for smooth monotone functions of a Gaussian vector

For a random vector `X : Ω → (ι → ℝ)` (`ι` finite) with Gaussian law (any mean, any — possibly
degenerate — covariance) and `cov(X i, X j) ≥ 0` for all `i, j`, and `f, g : (ι → ℝ) → ℝ` that are
`C¹`, bounded, Lipschitz and monotone: `E[f(X)] E[g(X)] ≤ E[f(X) g(X)]`
(`LQGMetric.Pitt.integral_mul_le_of_contDiff`).

Steps: (1) Gram representation `law(X) = law(m + (⟪v i, x⟫)ᵢ)` with `x` standard Gaussian and
`⟪v i, v j⟫ = cov(X i, X j)` (`LQGMetric.Pitt.exists_gram_map_eq`; the square-root construction
follows `LQGDimension.exists_gram_of_psdOn` (LQGDimension/Gaussian/Basic.lean) and the law
identification by characteristic functionals follows `QuantumZipper.RegUnif.fgmLaw_gram`
(QuantumZipper/Proofs/Zipper/FibreGaussMaxLaw.lean)); (2) the smooth core
`LQGMetric.Pitt.integral_mul_le_integral_mul_stdGaussian` (Pitt 1982), whose positivity
hypothesis `⟪F' x, G' y⟫ = Σᵢⱼ ∂ᵢf ∂ⱼg cov(Xᵢ, Xⱼ) ≥ 0` holds because monotone functions have
nonnegative partial derivatives.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Matrix MatrixOrder

namespace LQGMetric

namespace Pitt

variable {ι : Type*} [Fintype ι]

/-- The `i`-th unit vector of `ι → ℝ`. -/
def unitVec [DecidableEq ι] (i : ι) : ι → ℝ := fun j => if i = j then 1 else 0

omit [Fintype ι] in
lemma unitVec_nonneg [DecidableEq ι] (i : ι) : 0 ≤ unitVec i := fun j => by
  unfold unitVec; split_ifs <;> norm_num

lemma norm_unitVec_le [DecidableEq ι] (i : ι) : ‖unitVec i‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
    unfold unitVec; split_ifs <;> simp

lemma dual_apply_eq_sum [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (y : ι → ℝ) :
    L y = ∑ i, y i * L (unitVec i) := by
  have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) y
  exact this.trans (by simp only [smul_eq_mul]; rfl)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The map `x ↦ (⟪v i, x⟫)ᵢ`. -/
def gramCLM (v : ι → E) : E →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun i => innerSL ℝ (v i)

omit [Fintype ι] in
@[simp] lemma gramCLM_apply (v : ι → E) (x : E) (i : ι) : gramCLM v x i = ⟪v i, x⟫ := by
  simp [gramCLM]

lemma dual_comp_gramCLM [DecidableEq ι] (L : StrongDual ℝ (ι → ℝ)) (v : ι → E) :
    L.comp (gramCLM v) = innerSL ℝ (∑ i, L (unitVec i) • v i) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, dual_apply_eq_sum L, innerSL_apply_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gramCLM_apply, real_inner_smul_left, mul_comm]

lemma inner_sum_smul_sum_smul (a b : ι → ℝ) (v : ι → E) :
    ⟪∑ i, a i • v i, ∑ j, b j • v j⟫ = ∑ i, ∑ j, a i * b j * ⟪v i, v j⟫ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma memLp_coord {X : Ω → ι → ℝ} (hX : HasGaussianLaw X P) (i : ι) :
    MemLp (fun ω => X ω i) 2 P :=
  (hX.map_fun (ContinuousLinearMap.proj i)).memLp_two

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

/-- **Gram representation of a Gaussian vector.** -/
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
  have hYG : HasGaussianLaw Y γ := IsGaussian.hasGaussianLaw (by fun_prop)
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

end Pitt

end LQGMetric

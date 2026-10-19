/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGDimension/Gaussian/Concentration.lean (section Rotation).
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# Rotations of a product of two standard Gaussian measures

For a finite-dimensional real inner product space `E`, the map
`(x, y) ↦ (sin θ • x + cos θ • y, cos θ • x - sin θ • y)` of `E × E` preserves the product
of two standard Gaussian measures on `E`. The proof identifies that product with the standard
Gaussian measure on `WithLp 2 (E × E)`, where the map is a linear isometry.

The map is an orthogonal involution, not a rotation in general: its block matrix is symmetric
with square the identity, and its determinant is `(-1) ^ finrank E`. The identifiers keep the
`rot` prefix of the source.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real WithLp
open scoped RealInnerProductSpace

namespace LatticeProb.GaussConc

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The map `(x, y) ↦ (sin θ • x + cos θ • y, cos θ • x - sin θ • y)` of `E × E`. -/
def rotPair (θ : ℝ) (p : E × E) : E × E :=
  (Real.sin θ • p.1 + Real.cos θ • p.2, Real.cos θ • p.1 - Real.sin θ • p.2)

/-- The rotation `rotPair θ` is continuous. -/
lemma continuous_rotPair (θ : ℝ) : Continuous (rotPair (E := E) θ) := by
  unfold rotPair
  fun_prop

/-- The map `rotPair θ` as a linear map of `E × E`. -/
def rotPairLin (θ : ℝ) : E × E →ₗ[ℝ] E × E :=
  (Real.sin θ • LinearMap.fst ℝ E E + Real.cos θ • LinearMap.snd ℝ E E).prod
    (Real.cos θ • LinearMap.fst ℝ E E - Real.sin θ • LinearMap.snd ℝ E E)

/-- The map `rotPair θ` as a linear map of `WithLp 2 (E × E)`. -/
def rotLin (θ : ℝ) : WithLp 2 (E × E) →ₗ[ℝ] WithLp 2 (E × E) :=
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap ∘ₗ rotPairLin θ ∘ₗ
    (WithLp.linearEquiv 2 ℝ (E × E)).toLinearMap

/-- `rotLin θ` acts on `WithLp 2 (E × E)` through `rotPair θ`. -/
lemma rotLin_apply (θ : ℝ) (z : WithLp 2 (E × E)) : rotLin θ z = toLp 2 (rotPair θ (ofLp z)) :=
  rfl

/-- The rotation `rotLin θ` preserves the inner product of `WithLp 2 (E × E)`. -/
lemma inner_rotLin (θ : ℝ) (z w : WithLp 2 (E × E)) :
    ⟪rotLin θ z, rotLin θ w⟫ = ⟪z, w⟫ := by
  simp only [rotLin_apply, WithLp.prod_inner_apply, rotPair]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  have h := Real.sin_sq_add_cos_sq θ
  linear_combination (⟪(ofLp z).1, (ofLp w).1⟫ + ⟪(ofLp z).2, (ofLp w).2⟫) * h

variable [FiniteDimensional ℝ E]

/-- The map `rotPair θ` as a linear isometry equivalence of `WithLp 2 (E × E)`. -/
def rotLI (θ : ℝ) : WithLp 2 (E × E) ≃ₗᵢ[ℝ] WithLp 2 (E × E) :=
  ((rotLin θ).isometryOfInner (inner_rotLin θ)).toLinearIsometryEquiv rfl

/-- The linear isometry `rotLI θ` acts on `WithLp 2 (E × E)` through `rotPair θ`. -/
lemma rotLI_apply (θ : ℝ) (z : WithLp 2 (E × E)) : rotLI θ z = toLp 2 (rotPair θ (ofLp z)) :=
  rfl

variable [MeasurableSpace E] [BorelSpace E]

/-- The product of two standard Gaussian measures, seen in `WithLp 2 (E × E)`, is the standard
Gaussian measure there. -/
theorem map_toLp_prod_stdGaussian :
    ((stdGaussian E).prod (stdGaussian E)).map (toLp 2) = stdGaussian (WithLp 2 (E × E)) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  congr 1
  have h := WithLp.prod_norm_sq_eq_of_L2 t
  have h' : ((‖t‖ : ℂ)) ^ 2 = (‖(ofLp t).1‖ : ℂ) ^ 2 + (‖(ofLp t).2‖ : ℂ) ^ 2 := by
    exact_mod_cast h
  rw [h']
  ring

/-- The product of two standard Gaussian measures on `E × E` is the image of the standard
Gaussian measure on `WithLp 2 (E × E)` under `ofLp`. -/
theorem prod_stdGaussian_eq_map_ofLp :
    (stdGaussian E).prod (stdGaussian E) = (stdGaussian (WithLp 2 (E × E))).map ofLp := by
  rw [← map_toLp_prod_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have : (ofLp ∘ toLp 2 : E × E → E × E) = id := rfl
  rw [this, Measure.map_id]

/-- **Invariance**: `(x, y) ↦ (sin θ x + cos θ y, cos θ x - sin θ y)` preserves the
product of two standard Gaussian measures. -/
theorem measurePreserving_rotPair (θ : ℝ) :
    MeasurePreserving (rotPair θ) ((stdGaussian E).prod (stdGaussian E))
      ((stdGaussian E).prod (stdGaussian E)) := by
  refine ⟨(continuous_rotPair θ).measurable, ?_⟩
  rw [prod_stdGaussian_eq_map_ofLp, Measure.map_map (continuous_rotPair θ).measurable
    (by fun_prop)]
  have h : (rotPair θ ∘ ofLp : WithLp 2 (E × E) → E × E) = ofLp ∘ (rotLI (E := E) θ) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (rotLI (E := E) θ).continuous.measurable,
    stdGaussian_map]

end Rotation

namespace GaussProductRotationExample

/-- Invariance of the product of two standard Gaussians on the Euclidean plane, for the map
`rotPair` at the angle `π / 4`. -/
theorem measurePreserving_rotPair_pi_div_four :
    MeasurePreserving (rotPair (E := EuclideanSpace ℝ (Fin 2)) (Real.pi / 4))
      ((stdGaussian (EuclideanSpace ℝ (Fin 2))).prod (stdGaussian (EuclideanSpace ℝ (Fin 2))))
      ((stdGaussian (EuclideanSpace ℝ (Fin 2))).prod (stdGaussian (EuclideanSpace ℝ (Fin 2)))) :=
  measurePreserving_rotPair _

end GaussProductRotationExample

end LatticeProb.GaussConc

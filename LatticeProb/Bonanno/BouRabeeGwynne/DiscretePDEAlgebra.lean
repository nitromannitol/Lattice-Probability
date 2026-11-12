/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.DiscretePDEAlgebra at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators

namespace BouRabeeGwynne

/-!
# Exact algebra behind Section 2.1

The ambient finite type will later be instantiated by the finite set of vertices
`\bar V[U]`. Edge fields are extended by zero off the tiling edges.
-/

section Green

variable {V : Type*} [Fintype V]

/-- Equation (2.1), in the orientation convention `(w,v)` of the paper. -/
def discreteGrad (f : V → ℝ) (w v : V) : ℝ := f w - f v

/-- Equation (2.2). -/
def discreteDiv (θ : V → V → ℝ) (v : V) : ℝ := ∑ w, θ w v

/-- A vector field on oriented edges is antisymmetric under edge reversal. -/
def IsDiscreteVectorField (θ : V → V → ℝ) : Prop :=
  ∀ w v, θ w v = - θ v w

lemma sum_field_mul_head_eq_neg_tail
    (θ : V → V → ℝ) (f : V → ℝ) (hθ : IsDiscreteVectorField θ) :
    (∑ v, ∑ w, θ w v * f w) = - (∑ v, ∑ w, θ w v * f v) := by
  classical
  calc
    (∑ v, ∑ w, θ w v * f w)
        = ∑ w, ∑ v, θ v w * f v := by rw [Finset.sum_comm]
    _ = ∑ w, ∑ v, (- θ w v) * f v := by
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro v _
      rw [hθ v w]
    _ = - (∑ w, ∑ v, θ w v * f v) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
    _ = - (∑ v, ∑ w, θ w v * f v) := by
      congr 1
      rw [Finset.sum_comm]

/-- Lemma 2.1: discrete integration by parts. -/
theorem discrete_integration_by_parts
    (θ : V → V → ℝ) (f : V → ℝ) (hθ : IsDiscreteVectorField θ) :
    (∑ v, discreteDiv θ v * f v) =
      - (1 / 2 : ℝ) * (∑ v, ∑ w, θ w v * discreteGrad f w v) := by
  classical
  have hswap := sum_field_mul_head_eq_neg_tail θ f hθ
  have hdiv :
      (∑ v, discreteDiv θ v * f v) = ∑ v, ∑ w, θ w v * f v := by
    simp [discreteDiv, Finset.sum_mul]
  have hgrad :
      (∑ v, ∑ w, θ w v * discreteGrad f w v) =
        -2 * (∑ v, ∑ w, θ w v * f v) := by
    simp only [discreteGrad, mul_sub, Finset.sum_sub_distrib]
    rw [hswap]
    ring
  rw [hdiv, hgrad]
  ring

/-- Localized integration by parts when divergence vanishes on the support. -/
theorem discrete_integration_by_parts_zero
    (θ : V → V → ℝ) (f : V → ℝ) (hθ : IsDiscreteVectorField θ)
    (hdiv : ∀ v, f v ≠ 0 → discreteDiv θ v = 0) :
    (∑ v, ∑ w, θ w v * discreteGrad f w v) = 0 := by
  classical
  have hsum : (∑ v, discreteDiv θ v * f v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_cases hf : f v = 0
    · simp [hf]
    · simp [hdiv v hf]
  have hgreen := discrete_integration_by_parts θ f hθ
  rw [hsum] at hgreen
  linarith

end Green

section WeightedGraph

variable {V : Type*} [Fintype V]

/-- Symmetric finite conductance network, used after restricting the tiling. -/
structure FiniteConductanceNetwork (V : Type*) [Fintype V] where
  a : V → V → ℝ
  symm : ∀ v w, a v w = a w v
  nonneg : ∀ v w, 0 ≤ a v w
  loop_zero : ∀ v, a v v = 0

namespace FiniteConductanceNetwork

variable (N : FiniteConductanceNetwork V)

/-- Equation (1.4)/(2.4). -/
def laplacian (f : V → ℝ) (v : V) : ℝ :=
  ∑ w, N.a v w * (f w - f v)

/-- Weighted edge energy, with the factor `1/2` accounting for orientations. -/
noncomputable def energy (f : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ v, ∑ w, N.a v w * (f w - f v) ^ 2

/-- The weighted gradient field `a ∇f`. -/
def weightedGradient (f : V → ℝ) (w v : V) : ℝ :=
  N.a w v * discreteGrad f w v

lemma weightedGradient_antisymm (f : V → ℝ) :
    IsDiscreteVectorField (N.weightedGradient f) := by
  intro w v
  simp only [weightedGradient, discreteGrad]
  rw [N.symm w v]
  ring

lemma div_weightedGradient_eq_laplacian (f : V → ℝ) (v : V) :
    discreteDiv (N.weightedGradient f) v = N.laplacian f v := by
  simp only [discreteDiv, weightedGradient, laplacian, discreteGrad]
  apply Finset.sum_congr rfl
  intro w _
  rw [N.symm w v]

/-- Green identity for the conductance Laplacian. -/
theorem green_laplacian (f g : V → ℝ) :
    (∑ v, N.laplacian f v * g v) =
      -(1 / 2 : ℝ) *
        (∑ v, ∑ w, N.a v w * (f w - f v) * (g w - g v)) := by
  have h := discrete_integration_by_parts (N.weightedGradient f) g
    (N.weightedGradient_antisymm f)
  simpa only [div_weightedGradient_eq_laplacian, weightedGradient,
    discreteGrad, N.symm, mul_assoc] using h

/-- Constants are discrete harmonic. -/
@[simp] lemma laplacian_const (c : ℝ) (v : V) : N.laplacian (fun _ => c) v = 0 := by
  simp [laplacian]

/-- Energy is nonnegative. -/
lemma energy_nonneg (f : V → ℝ) : 0 ≤ N.energy f := by
  unfold energy
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro v _
    apply Finset.sum_nonneg
    intro w _
    exact mul_nonneg (N.nonneg v w) (sq_nonneg (f w - f v))

end FiniteConductanceNetwork

end WeightedGraph

section DualDirichlet

variable {ι : Type*} [Fintype ι]

/-- Pure quadratic minimization used in Lemma 2.3. -/
theorem weighted_quadratic_minimizer
    (a x y : ι → ℝ)
    (ha : ∀ i, 0 < a i)
    (horth : ∑ i, (y i - x i) * x i / a i = 0) :
    (∑ i, x i ^ 2 / a i) ≤ ∑ i, y i ^ 2 / a i := by
  classical
  have hnonneg : 0 ≤ ∑ i, (y i - x i) ^ 2 / a i := by
    exact Finset.sum_nonneg fun i _ =>
      div_nonneg (sq_nonneg (y i - x i)) (le_of_lt (ha i))
  have hdecomp :
      (∑ i, y i ^ 2 / a i) =
        (∑ i, x i ^ 2 / a i)
          + 2 * (∑ i, (y i - x i) * x i / a i)
          + (∑ i, (y i - x i) ^ 2 / a i) := by
    calc
      (∑ i, y i ^ 2 / a i)
          = ∑ i, (x i ^ 2 / a i
              + 2 * ((y i - x i) * x i / a i)
              + (y i - x i) ^ 2 / a i) := by
              apply Finset.sum_congr rfl
              intro i _
              have hane : a i ≠ 0 := ne_of_gt (ha i)
              field_simp [hane]
              ring
      _ = (∑ i, x i ^ 2 / a i)
          + 2 * (∑ i, (y i - x i) * x i / a i)
          + (∑ i, (y i - x i) ^ 2 / a i) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [horth] at hdecomp
  nlinarith

end DualDirichlet

end BouRabeeGwynne

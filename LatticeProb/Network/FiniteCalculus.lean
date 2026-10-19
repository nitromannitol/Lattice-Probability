/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/DiscretePDEAlgebra.lean.
-/
import LatticeProb.Network.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Discrete calculus on a finite vertex type

On a finite vertex type `V`, a function `f : V → ℝ` has the discrete gradient
`discreteGrad f w v = f w - f v` along each ordered pair, and an edge field `θ : V → V → ℝ`
has the discrete divergence `discreteDiv θ v = ∑ w, θ w v`. An edge field is antisymmetric when
`θ w v = -θ v w`.

The integration-by-parts identities are the summation-by-parts identities for these
operators. Their weighted form, with a conductance `c` of a graph `G`, gives the Green identity
for the network Laplacian `netLaplacian G c`, which is derived from the summation-by-parts
identity `formOn_eq_neg_two_mul` for graphs. The energy of a function is nonnegative by
`energyOn_nonneg`. The last result is the minimization of a weighted quadratic form under a
weighted orthogonality condition.
-/

namespace LatticeProb.Network

section Calculus

variable {V : Type*}

/-- The discrete gradient of `f` along the ordered pair `(w, v)`. -/
def discreteGrad (f : V → ℝ) (w v : V) : ℝ := f w - f v

/-- An edge field is antisymmetric under reversal of the orientation of an edge. -/
def IsDiscreteVectorField (θ : V → V → ℝ) : Prop :=
  ∀ w v, θ w v = -θ v w

/-- The conductance-weighted gradient `c(w, v) (f w - f v)` of `f`, as an edge field. -/
def weightedGradient (c : V → V → ℝ) (f : V → ℝ) (w v : V) : ℝ :=
  c w v * discreteGrad f w v

/-- The weighted gradient of a function is antisymmetric when the conductance is symmetric. -/
theorem weightedGradient_isDiscreteVectorField {c : V → V → ℝ}
    (hsymm : ∀ w v, c w v = c v w) (f : V → ℝ) :
    IsDiscreteVectorField (weightedGradient c f) := by
  intro w v
  simp only [weightedGradient, discreteGrad]
  rw [hsymm w v]
  ring

variable [Fintype V]

/-- The discrete divergence of an edge field `θ` at `v`: the sum of the entries `θ w v` over
all `w`. -/
def discreteDiv (θ : V → V → ℝ) (v : V) : ℝ := ∑ w, θ w v

theorem sum_field_mul_head_eq_neg_tail
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

/-- Discrete integration by parts: the divergence of an antisymmetric field against `f` equals
`-1/2` times the sum of the field against the discrete gradient of `f`. -/
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

/-- Integration by parts for a field whose divergence vanishes wherever `f` is nonzero: the
gradient pairing of the field with `f` is zero. -/
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

/-- Minimization of a weighted square sum: if `x` is weighted-orthogonal to `y - x`, then the
weighted square sum of `x` is at most that of `y`. -/
theorem weighted_quadratic_minimizer {ι : Type*} [Fintype ι]
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

end Calculus

section Network

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [G.LocallyFinite]

/-- The divergence of the weighted gradient is the network Laplacian. -/
theorem discreteDiv_weightedGradient_eq_netLaplacian {c : V → V → ℝ} (hc : IsCond G c)
    (f : V → ℝ) (v : V) :
    discreteDiv (weightedGradient c f) v = netLaplacian G c f v := by
  have hconv : netLaplacian G c f v = ∑ w, c v w * (f w - f v) := by
    unfold netLaplacian
    exact sum_neighborFinset_eq_sum v Finset.univ (fun w => c v w * (f w - f v))
      (fun y hy => by simp [hc.zero_of_not_adj hy]) (fun y _ _ => Finset.mem_univ y)
  rw [hconv]
  unfold discreteDiv weightedGradient discreteGrad
  exact Finset.sum_congr rfl fun w _ => by rw [hc.symm w v]

/-- **Green identity for the network Laplacian.** For a conductance `c` of a locally finite
graph, `∑ v, Δf(v) g(v) = -1/2 ∑_v ∑_w c(v,w) (f w - f v) (g w - g v)`, where the inner sum
runs over all `w`, and `c(v, w) = 0` for non-edges. -/
theorem green_netLaplacian {c : V → V → ℝ} (hc : IsCond G c) (f g : V → ℝ) :
    ∑ v, netLaplacian G c f v * g v =
      -(1 / 2 : ℝ) * ∑ v, ∑ w, c v w * (f w - f v) * (g w - g v) := by
  have h := formOn_eq_neg_two_mul hc Finset.univ Finset.univ f g
    (fun x hx => absurd (Finset.mem_univ x) hx) (Finset.Subset.refl _)
    (fun x _ y _ => Finset.mem_univ y)
  have hinner : ∀ x : V, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) * (g x - g y) =
      ∑ w, c x w * (f w - f x) * (g w - g x) := by
    intro x
    rw [sum_neighborFinset_eq_sum x Finset.univ (fun y => c x y * (f x - f y) * (g x - g y))
      (fun y hy => by simp [hc.zero_of_not_adj hy]) (fun y _ _ => Finset.mem_univ y)]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hform : formOn G c Finset.univ f g =
      ∑ v, ∑ w, c v w * (f w - f v) * (g w - g v) :=
    Finset.sum_congr rfl fun x _ => hinner x
  have hsum : ∑ v, netLaplacian G c f v * g v = ∑ v, g v * netLaplacian G c f v :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hsum, ← hform, h]
  ring

/-- The Dirichlet energy of `f`: half of the sum over ordered pairs of `c(v, w) (f w - f v)²`.
It is half of `energyOn` taken over all vertices. -/
noncomputable def dirichletEnergy (c : V → V → ℝ) (f : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ v, ∑ w, c v w * (f w - f v) ^ 2

/-- The Dirichlet energy is nonnegative for a conductance. It is obtained from `energyOn_nonneg`
by writing the neighbour sum over all vertices. -/
theorem dirichletEnergy_nonneg {c : V → V → ℝ} (hc : IsCond G c) (f : V → ℝ) :
    0 ≤ dirichletEnergy c f := by
  have hconv : energyOn G c Finset.univ f = ∑ v, ∑ w, c v w * (f w - f v) ^ 2 := by
    rw [energyOn_eq_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sum_neighborFinset_eq_sum x Finset.univ (fun y => c x y * (f x - f y) ^ 2)
      (fun y hy => by simp [hc.zero_of_not_adj hy]) (fun y _ _ => Finset.mem_univ y)]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hnonneg : 0 ≤ ∑ v, ∑ w, c v w * (f w - f v) ^ 2 := by
    rw [← hconv]
    exact energyOn_nonneg hc Finset.univ f
  unfold dirichletEnergy
  exact mul_nonneg (by norm_num) hnonneg

/-! ### Nonvacuity examples on the path `0 – 1 – 2` with unit conductance -/

namespace CalculusExamples

open SimpleGraph

@[reducible] noncomputable def pathLocallyFinite : (pathGraph 3).LocallyFinite :=
  fun _ => Fintype.ofFinite _

attribute [local instance] pathLocallyFinite

/-- The Green identity applies to the unit-conductance path. -/
theorem pathGraph_green (f g : Fin 3 → ℝ) :
    ∑ v, netLaplacian (pathGraph 3) (unitCond (pathGraph 3)) f v * g v =
      -(1 / 2 : ℝ) * ∑ v, ∑ w, unitCond (pathGraph 3) v w * (f w - f v) * (g w - g v) :=
  green_netLaplacian (isCond_unitCond (G := pathGraph 3)) f g

/-- Integration by parts applies to the weighted gradient of a function on the unit-conductance
path, which is an antisymmetric field. -/
theorem pathGraph_integration_by_parts (f g : Fin 3 → ℝ) :
    ∑ v, discreteDiv (weightedGradient (unitCond (pathGraph 3)) f) v * g v =
      -(1 / 2 : ℝ) * ∑ v, ∑ w, weightedGradient (unitCond (pathGraph 3)) f w v *
        discreteGrad g w v :=
  discrete_integration_by_parts _ g
    (weightedGradient_isDiscreteVectorField (isCond_unitCond (G := pathGraph 3)).symm f)

/-- The zero edge field is antisymmetric with zero divergence, so the localized form of
integration by parts applies to it with any function. -/
theorem zero_field_integration_by_parts (g : Fin 3 → ℝ) :
    ∑ v, ∑ w, (fun _ _ : Fin 3 => (0 : ℝ)) w v * discreteGrad g w v = 0 :=
  discrete_integration_by_parts_zero (fun _ _ => 0) g (fun w v => by simp)
    (fun v _ => by simp [discreteDiv])

/-- The Dirichlet energy of any function on the unit-conductance path is nonnegative. -/
theorem pathGraph_dirichletEnergy_nonneg (f : Fin 3 → ℝ) :
    0 ≤ dirichletEnergy (unitCond (pathGraph 3)) f :=
  dirichletEnergy_nonneg (isCond_unitCond (G := pathGraph 3)) f

/-- Weighted quadratic minimization on two points with unit weights: `x = 0` is orthogonal to
`y - x`, and `0 ≤ 1 + 1`. -/
theorem weighted_quadratic_minimizer_example :
    ∑ i : Fin 2, (fun _ => (0 : ℝ)) i ^ 2 / (fun _ => (1 : ℝ)) i ≤
      ∑ i : Fin 2, (fun _ => (1 : ℝ)) i ^ 2 / (fun _ => (1 : ℝ)) i :=
  weighted_quadratic_minimizer (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
    (by simp)

end CalculusExamples

end Network

end LatticeProb.Network

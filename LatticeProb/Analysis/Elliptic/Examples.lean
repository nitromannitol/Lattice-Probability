import LatticeProb.Analysis.Elliptic.Dirichlet

/-!
# Euclidean ball and quadratic Dirichlet examples

The open Euclidean unit ball is a nonempty bounded regular domain. A quadratic polynomial
provides a nonzero classical solution with the prescribed Laplacian normalization, and its
datum has finite Euclidean Hölder norm on the closed ball.
-/

namespace LatticeProb.Elliptic

open LatticeProb.Euclidean.Lattice
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-- The open Euclidean unit ball on the coordinate carrier. -/
def unitBall (d : ℕ) : Set (Fin d → ℝ) := {x | radius x < 1}

/-- Membership in the Euclidean unit ball is the strict quadratic sublevel inequality. -/
theorem mem_unitBall_iff (x : Fin d → ℝ) : x ∈ unitBall d ↔ ∑ k, x k ^ 2 < 1 := by
  have hs := radius_sq x
  have hn := radius_nonneg x
  change radius x < 1 ↔ _
  constructor <;> intro h <;> nlinarith

/-- Euclidean radius bounds give bounded sets in the coordinate topology. -/
theorem isBounded_radius_sublevel (R : ℝ) :
    Bornology.IsBounded {x : Fin d → ℝ | radius x < R} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨|R| + 1, fun x hx => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hR : R ≤ |R| + 1 := (le_abs_self R).trans (by linarith)
  exact (abs_coord_le_radius x i).trans (hx.le.trans hR)

/-- The quadratic unit ball is convex. -/
theorem convex_unitBall (d : ℕ) : Convex ℝ (unitBall d) := by
  intro x hx y hy a b ha hb hab
  rw [mem_unitBall_iff] at hx hy ⊢
  have hcoord (k : Fin d) :
      (a * x k + b * y k) ^ 2 ≤ a * x k ^ 2 + b * y k ^ 2 := by
    have hsq := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x k - y k))
    have hb_eq : b = 1 - a := by linarith
    calc
      (a * x k + b * y k) ^ 2 =
          a * x k ^ 2 + b * y k ^ 2 - a * b * (x k - y k) ^ 2 := by
        rw [hb_eq]
        ring
      _ ≤ a * x k ^ 2 + b * y k ^ 2 := sub_le_self _ hsq
  calc
    ∑ k, (a • x + b • y) k ^ 2 ≤ ∑ k, (a * x k ^ 2 + b * y k ^ 2) :=
      Finset.sum_le_sum (fun k _ => hcoord k)
    _ = a * (∑ k, x k ^ 2) + b * (∑ k, y k ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ < 1 := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hy
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        calc
          a * (∑ k, x k ^ 2) + b * (∑ k, y k ^ 2) < a * 1 + b * 1 :=
            add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx hapos)
              (mul_le_mul_of_nonneg_left hy.le hb)
          _ = 1 := by linarith

/-- Every point in the closure of the unit ball has Euclidean radius at most one. -/
theorem radius_le_one_of_mem_closure_unitBall {x : Fin d → ℝ}
    (hx : x ∈ closure (unitBall d)) : radius x ≤ 1 := by
  have hsubset : closure (unitBall d) ⊆ {y | radius y ≤ 1} := by
    apply (isClosed_le (radius_continuous d) continuous_const).closure_subset_iff.mpr
    intro y hy
    change radius y ≤ 1
    exact (show radius y < 1 from hy).le
  exact hsubset hx

/-- The quadratic defining function has a nonzero derivative at each of its zeros. -/
theorem regular_quadratic_zero (x : Fin d → ℝ) (hx : (∑ k, x k ^ 2) - 1 = 0) :
    fderiv ℝ (fun y : Fin d → ℝ => (∑ k, y k ^ 2) - 1) x ≠ 0 := by
  have hex : ∃ i, x i ≠ 0 := by
    by_contra! h
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, zero_sub] at hx
    norm_num at hx
  obtain ⟨i, hi⟩ := hex
  intro hz
  have heq : (fun y : Fin d → ℝ => (∑ k, y k ^ 2) - 1) =
      (fun y => -1 + 1 * ∑ k, y k ^ 2) := by ext y; ring
  have hpartial := partialDeriv_affine_sum_sq (-1) 1 i x
  rw [← heq, partialDeriv, hz] at hpartial
  simp only [zero_apply, mul_one] at hpartial
  exact hi (by linarith)

/-- Affine functions of squared radius have finite `C^{2,σ}` norm on bounded sets. -/
theorem c2HolderNorm_affine_sum_sq_lt_top (σ c b : ℝ)
    {S : Set (Fin d → ℝ)} (hS : Bornology.IsBounded S) :
    c2HolderNorm σ S (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) < ⊤ := by
  have hzero (i j : Fin d) :
      holderSeminorm σ S
        (secondPartial i j (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2)) = 0 := by
    simp only [show secondPartial i j (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) =
      (fun _ => if i = j then 2 * b else 0) from
        funext (secondPartial_affine_sum_sq c b i j), holderSeminorm_const]
  simp only [c2HolderNorm, ENNReal.add_lt_top, ENNReal.sum_lt_top, Finset.mem_univ,
    forall_const]
  refine ⟨⟨⟨supNorm_lt_top_of_continuous hS (by fun_prop), ?_⟩, ?_⟩, ?_⟩
  · intro i
    rw [show partialDeriv i (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) =
      (fun y => 2 * b * y i) from funext (partialDeriv_affine_sum_sq c b i)]
    exact supNorm_lt_top_of_continuous hS (by fun_prop)
  · intro i j
    rw [show secondPartial i j (fun y : Fin d → ℝ => c + b * ∑ k, y k ^ 2) =
      (fun _ => if i = j then 2 * b else 0) from
        funext (secondPartial_affine_sum_sq c b i j)]
    exact supNorm_lt_top_of_continuous hS continuous_const
  · intro i j
    rw [hzero]
    exact ENNReal.zero_lt_top

/-- The open Euclidean unit ball is a bounded domain with a regular quadratic defining function. -/
theorem isC2HolderDomain_unitBall (σ : ℝ) : IsC2HolderDomain σ (unitBall d) := by
  refine ⟨isOpen_lt (radius_continuous d) continuous_const,
    (convex_unitBall d).isConnected ?_, isBounded_radius_sublevel 1, ?_⟩
  · exact ⟨0, by simp [unitBall, radius]⟩
  · refine ⟨fun x => (∑ k, x k ^ 2) - 1, by fun_prop, ?_, ?_,
      regular_quadratic_zero⟩
    · intro R
      have heq : (fun x : Fin d → ℝ => (∑ k, x k ^ 2) - 1) =
          (fun x => -1 + 1 * ∑ k, x k ^ 2) := by ext x; ring
      rw [heq]
      exact c2HolderNorm_affine_sum_sq_lt_top σ (-1) 1 (isBounded_radius_sublevel R)
    · ext x
      rw [mem_unitBall_iff]
      change (∑ k, x k ^ 2) < 1 ↔ (∑ k, x k ^ 2) - 1 < 0
      constructor <;> intro h <;> linarith

/-- The frontier of the Euclidean unit ball is its quadratic level set. -/
theorem frontier_unitBall (d : ℕ) :
    frontier (unitBall d) = {x | ∑ k, x k ^ 2 = 1} := by
  have heq : unitBall d = {x : Fin d → ℝ | (∑ k, x k ^ 2) - 1 < 0} := by
    ext x
    rw [mem_unitBall_iff]
    change (∑ k, x k ^ 2) < 1 ↔ (∑ k, x k ^ 2) - 1 < 0
    constructor <;> intro h <;> linarith
  rw [heq, frontier_sublevel_eq_zero (by fun_prop) regular_quadratic_zero]
  ext x
  simp only [Set.mem_setOf_eq, sub_eq_zero]

/-- The quadratic function solves the Dirichlet equation with its explicitly computed datum. -/
theorem quadratic_isClassicalDirichletSolution (μ a₀ : ℝ) :
    IsClassicalDirichletSolution (unitBall d) μ a₀
      (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀)
      (fun x => 1 - ∑ k, x k ^ 2) := by
  refine ⟨(show ContDiff ℝ 2 (fun x : Fin d → ℝ => 1 - ∑ k, x k ^ 2) by
    fun_prop).contDiffOn, (by fun_prop), ?_, ?_⟩
  · intro x hx
    rw [frontier_unitBall] at hx
    change (∑ k, x k ^ 2) = 1 at hx
    exact sub_eq_zero.mpr hx.symm
  · intro x _
    have heq : (fun x : Fin d → ℝ => 1 - ∑ k, x k ^ 2) =
        (fun x => 1 + (-1) * ∑ k, x k ^ 2) := by ext y; ring
    rw [heq, laplacian_affine_sum_sq]
    ring

/-- Squared radius has a Euclidean Hölder increment bound on the closed unit ball. -/
theorem abs_sub_sum_sq_le_rpow {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {x y : Fin d → ℝ} (hx : radius x ≤ 1) (hy : radius y ≤ 1) :
    |(∑ k, x k ^ 2) - ∑ k, y k ^ 2| ≤ 2 * radius (x - y) ^ σ := by
  have hx0 := radius_nonneg x
  have hy0 := radius_nonneg y
  have hq : |radius x ^ 2 - radius y ^ 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hlip : |radius x ^ 2 - radius y ^ 2| ≤ 2 * radius (x - y) := by
    calc
      |radius x ^ 2 - radius y ^ 2| =
          |radius x - radius y| * (radius x + radius y) := by
        rw [← abs_of_nonneg (add_nonneg hx0 hy0), ← abs_mul]
        congr 1
        ring
      _ ≤ radius (x - y) * (radius x + radius y) :=
        mul_le_mul_of_nonneg_right (radius_difference x y) (add_nonneg hx0 hy0)
      _ ≤ 2 * radius (x - y) := by
        nlinarith [radius_nonneg (x - y)]
  rw [← radius_sq, ← radius_sq]
  by_cases hr : radius (x - y) ≤ 1
  · exact hlip.trans (mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one (radius_nonneg _) hr hσ1.le) (by norm_num))
  · have hp := Real.one_le_rpow (le_of_not_ge hr) hσ.le
    linarith

/-- Affine quadratic data have finite Euclidean Hölder norm on the closed unit ball. -/
theorem c0HolderNorm_affine_sum_sq_closure_unitBall_lt_top {σ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (c b : ℝ) :
    c0HolderNorm σ (closure (unitBall d))
      (fun x : Fin d → ℝ => c + b * ∑ k, x k ^ 2) < ⊤ := by
  apply ENNReal.add_lt_top.mpr
  refine ⟨supNorm_lt_top_of_continuous (isBounded_radius_sublevel 1).closure
    (by fun_prop), holderSeminorm_lt_top_of_bound (2 * |b|) ?_⟩
  intro x hx y hy hxy
  have hp := Real.rpow_pos_of_pos (radius_pos (sub_ne_zero.mpr hxy)) σ
  apply (div_le_iff₀ hp).mpr
  calc
    |c + b * ∑ k, x k ^ 2 - (c + b * ∑ k, y k ^ 2)| =
        |b| * |(∑ k, x k ^ 2) - ∑ k, y k ^ 2| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |b| * (2 * radius (x - y) ^ σ) :=
      mul_le_mul_of_nonneg_left (abs_sub_sum_sq_le_rpow hσ hσ1
        (radius_le_one_of_mem_closure_unitBall hx)
        (radius_le_one_of_mem_closure_unitBall hy)) (abs_nonneg b)
    _ = _ := by rw [← mul_assoc, mul_comm (|b|) 2]

/-- The datum of the quadratic Dirichlet solution has finite Euclidean Hölder norm. -/
theorem quadratic_datum_c0HolderNorm_lt_top {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (μ a₀ : ℝ) :
    c0HolderNorm σ (closure (unitBall d))
      (fun x : Fin d → ℝ => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀) < ⊤ := by
  have heq : (fun x : Fin d → ℝ => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀) =
      (fun x => (μ + 2 * d * a₀) + (-μ) * ∑ k, x k ^ 2) := by ext x; ring
  rw [heq]
  exact c0HolderNorm_affine_sum_sq_closure_unitBall_lt_top hσ hσ1 _ _

/-- Positive diffusion and nonnegative mass give a nonzero solution and positive datum at zero. -/
theorem quadratic_nonvacuity (hd : 1 ≤ d) {σ μ a₀ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ < 1) (hμ : 0 ≤ μ) (ha₀ : 0 < a₀) :
    IsC2HolderDomain σ (unitBall d) ∧
      IsClassicalDirichletSolution (unitBall d) μ a₀
        (fun x => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀)
        (fun x => 1 - ∑ k, x k ^ 2) ∧
      c0HolderNorm σ (closure (unitBall d))
        (fun x : Fin d → ℝ => μ * (1 - ∑ k, x k ^ 2) + 2 * d * a₀) < ⊤ ∧
      (0 : Fin d → ℝ) ∈ unitBall d ∧
      (1 - ∑ k : Fin d, (0 : Fin d → ℝ) k ^ 2) = 1 ∧
      0 < μ * (1 - ∑ k : Fin d, (0 : Fin d → ℝ) k ^ 2) + 2 * d * a₀ := by
  refine ⟨isC2HolderDomain_unitBall σ, quadratic_isClassicalDirichletSolution μ a₀,
    quadratic_datum_c0HolderNorm_lt_top hσ hσ1 μ a₀, ?_, ?_, ?_⟩
  · simp [unitBall, radius]
  · simp
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    simpa only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, sub_zero, mul_one] using
      add_pos_of_nonneg_of_pos hμ (mul_pos (mul_pos (by norm_num) hdpos) ha₀)

end

end LatticeProb.Elliptic

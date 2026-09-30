/- Uniform Taylor bounds for symmetric second differences.

Moved from Parking-Sharpness.
-/
import Mathlib

open Set

namespace LatticeProb.Scaling.SymmetricTaylor

/-- The quadratic Taylor polynomial, written with ordinary derivatives. -/
theorem taylorWithinEval_two {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {a b : ℝ} (hab : a ≠ b) :
    taylorWithinEval f 2 (uIcc a b) a b =
      f a + deriv f a * (b - a) + deriv (deriv f) a * (b - a) ^ 2 / 2 := by
  have hu : UniqueDiffOn ℝ (uIcc a b) := uniqueDiffOn_Icc (by
    exact min_lt_max.mpr hab)
  have h1 : iteratedDerivWithin 1 f (uIcc a b) a = deriv f a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc),
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (uIcc a b) a = deriv (deriv f) a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt (left_mem_uIcc)]
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  norm_num [taylorWithinEval_succ, h1, h2, smul_eq_mul]
  ring

/-- A bounded third derivative controls the quadratic remainder in either direction. -/
theorem abs_quadratic_remainder_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {C : ℝ} (hC : ∀ y, |iteratedDeriv 3 f y| ≤ C) (a b : ℝ) :
    |f b - (f a + deriv f a * (b - a) + deriv (deriv f) a * (b - a)^2 / 2)|
      ≤ C * |b - a| ^ 3 / 6 := by
  by_cases hab : a = b
  · subst b; simp
  obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hab hf.contDiffOn
  rw [taylorWithinEval_two hf hab] at hy
  rw [hy, abs_div, abs_mul, abs_pow]
  norm_num
  gcongr
  exact hC y

/-- The odd linear terms cancel in the symmetric second difference. -/
theorem abs_symmetric_second_sub_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {C : ℝ} (hC : ∀ y, |iteratedDeriv 3 f y| ≤ C) (x h : ℝ) :
    |f (x + h) + f (x - h) - 2 * f x - h ^ 2 * deriv (deriv f) x|
      ≤ C * |h| ^ 3 / 3 := by
  have hp := abs_quadratic_remainder_le hf hC x (x + h)
  have hm := abs_quadratic_remainder_le hf hC x (x - h)
  have heq : f (x + h) + f (x - h) - 2 * f x - h ^ 2 * deriv (deriv f) x =
      (f (x + h) - (f x + deriv f x * ((x + h) - x) +
        deriv (deriv f) x * ((x + h) - x)^2 / 2)) +
      (f (x - h) - (f x + deriv f x * ((x - h) - x) +
        deriv (deriv f) x * ((x - h) - x)^2 / 2)) := by ring
  rw [heq]
  have hadd := abs_add_le
    (f (x + h) - (f x + deriv f x * ((x + h) - x) + deriv (deriv f) x * ((x + h) - x)^2 / 2))
    (f (x - h) - (f x + deriv f x * ((x - h) - x) + deriv (deriv f) x * ((x - h) - x)^2 / 2))
  have habs : |x - h - x| = |h| := by rw [show x - h - x = -h by ring, abs_neg]
  simp only [add_sub_cancel_left, habs] at hp hm hadd ⊢
  linarith


noncomputable section

/-- Differentiation in a fixed coordinate direction of a function of `d` real variables. -/
def coordDeriv {d : ℕ} (i : Fin d) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The coordinate derivative of a smooth function is smooth. -/
theorem contDiff_coordDeriv {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordDeriv i f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- The coordinate derivative of a compactly supported function has compact support. -/
theorem hasCompactSupport_coordDeriv {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : HasCompactSupport f) (i : Fin d) : HasCompactSupport (coordDeriv i f) :=
  hf.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)

/-- The ordinary derivative of a one-coordinate slice agrees with the coordinate derivative
evaluated on that slice. -/
theorem deriv_update_eq_coordDeriv {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (i : Fin d) (x : Fin d → ℝ) (s : ℝ) :
    deriv (fun t => f (Function.update x i t)) s = coordDeriv i f (Function.update x i s) := by
  exact ((hf _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_update x i s)).deriv

/-- The third ordinary derivative of a one-coordinate slice agrees with the thrice-iterated
coordinate derivative in that same direction. -/
theorem iteratedDeriv_update_three {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (x : Fin d → ℝ) (s : ℝ) :
    iteratedDeriv 3 (fun t => f (Function.update x i t)) s =
      coordDeriv i (coordDeriv i (coordDeriv i f)) (Function.update x i s) := by
  have h1 := contDiff_coordDeriv hf i
  have h2 := contDiff_coordDeriv h1 i
  have heq1 : deriv (fun t => f (Function.update x i t)) =
      fun t => coordDeriv i f (Function.update x i t) :=
    funext fun t => deriv_update_eq_coordDeriv (hf.differentiable (by simp)) i x t
  have heq2 : deriv (fun t => coordDeriv i f (Function.update x i t)) =
      fun t => coordDeriv i (coordDeriv i f) (Function.update x i t) :=
    funext fun t => deriv_update_eq_coordDeriv (h1.differentiable (by simp)) i x t
  rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, show 2 = 1 + 1 from rfl,
    iteratedDeriv_succ, iteratedDeriv_one, heq1, heq2]
  exact deriv_update_eq_coordDeriv (h2.differentiable (by simp)) i x s

/-- A smooth compactly supported function of `d` variables has a single constant bounding the
third derivative of every one-coordinate slice, uniformly over the coordinate, the base point
and the slice parameter. -/
theorem exists_uniform_third_coordinate_bound {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (x : Fin d → ℝ) (s : ℝ),
      |iteratedDeriv 3 (fun t => f (Function.update x i t)) s| ≤ C := by
  classical
  have hb : ∀ i : Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordDeriv i (coordDeriv i (coordDeriv i f)) x| ≤ C := by
    intro i
    have hc := (contDiff_coordDeriv (contDiff_coordDeriv (contDiff_coordDeriv hf i) i) i).continuous.abs
    have hs' := (hasCompactSupport_coordDeriv (hasCompactSupport_coordDeriv
      (hasCompactSupport_coordDeriv hs i) i) i).abs
    obtain ⟨C, hC⟩ := hc.bddAbove_range_of_hasCompactSupport hs'
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    exact (hC ⟨x, rfl⟩).trans (le_max_left _ _)
  choose C hC hbound using hb
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i x s => ?_⟩
  rw [iteratedDeriv_update_three hf]
  exact (hbound i _).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))


/-- The symmetric second difference of a smooth compactly supported function of `d` variables,
along any single coordinate direction, is uniformly controlled by the cube of the step size. -/
theorem exists_uniform_coordinate_taylor_bound {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (x : Fin d → ℝ) (h : ℝ),
      |f (Function.update x i (x i + h)) + f (Function.update x i (x i - h)) - 2 * f x
        - h ^ 2 * deriv (deriv (fun t => f (Function.update x i t))) (x i)|
        ≤ C * |h| ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_third_coordinate_bound hf hs
  refine ⟨C / 3, by positivity, fun i x h => ?_⟩
  have hc : ContDiff ℝ 3 (fun t => f (Function.update x i t)) :=
    (hf.of_le (by exact WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))).comp (contDiff_update 3 x i)
  have hb := abs_symmetric_second_sub_le hc (hbound i x) (x i) h
  simpa only [Function.update_eq_self, div_mul_eq_mul_div] using hb

end

end LatticeProb.Scaling.SymmetricTaylor

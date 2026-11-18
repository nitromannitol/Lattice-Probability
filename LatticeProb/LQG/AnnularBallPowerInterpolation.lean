import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Ball power bounds from an origin bound and an off-origin bound

Let `v` be a measure on a seminormed group. Suppose that balls centered at the origin
satisfy `v (ball 0 s) ≤ A s ^ a`, and that every ball `ball z r` with `2 r < ‖z‖`
satisfies `v (ball z r) ≤ C ‖z‖ ^ (-g) r ^ κ`. Then every ball `ball z r` with
`‖z‖ ≤ R` and `r ≤ 1` has mass at most `K r ^ β`, where
`β = min a (κ a / (a + g))` and `K` is explicit.

A ball whose center is within distance `2 r` of the origin lies in `ball 0 (3 r)`.
A ball with `2 r < ‖z‖` lies in `ball 0 (3 ‖z‖ / 2)`; the weighted geometric mean
of the two available bounds, with weights `g / (a + g)` and `a / (a + g)`, cancels
the power of `‖z‖`.

This is the annular step in the proof of uniform ball bounds for Gaussian
multiplicative chaos approximants with a logarithmic singularity at the origin:
the origin estimate controls balls near the singularity, and the regular estimate,
weighted by the singular density `‖x‖ ^ (-γ ^ 2)`, controls balls away from it.
-/

open MeasureTheory Metric

namespace LatticeProb.LQG

/-- The minimum of two nonnegative reals is at most each of their weighted
geometric means. -/
theorem min_le_rpow_mul_rpow {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min x y ≤ x ^ (1 - θ) * y ^ θ := by
  have hm : 0 ≤ min x y := le_min hx hy
  calc min x y = min x y ^ ((1 - θ) + θ) := by
          rw [sub_add_cancel, Real.rpow_one]
    _ = min x y ^ (1 - θ) * min x y ^ θ :=
          Real.rpow_add' hm (by rw [sub_add_cancel]; exact one_ne_zero)
    _ ≤ x ^ (1 - θ) * y ^ θ :=
          mul_le_mul (Real.rpow_le_rpow hm (min_le_left x y) (by linarith))
            (Real.rpow_le_rpow hm (min_le_right x y) hθ0)
            (Real.rpow_nonneg hm _) (Real.rpow_nonneg hx _)

/-- For `0 < d`, the weighted geometric mean of `A ((3 / 2) d) ^ a` and
`C d ^ (-g) r ^ κ`, with weights `1 - a / (a + g)` and `a / (a + g)`, does not
depend on `d`. -/
theorem rpow_mul_rpow_offOrigin_eq {A C a g κ d r : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ha : 0 < a) (hg : 0 ≤ g) (hd : 0 < d) (hr : 0 ≤ r) :
    (A * (3 / 2 * d) ^ a) ^ (1 - a / (a + g)) * (C * d ^ (-g) * r ^ κ) ^ (a / (a + g)) =
      (A * (3 / 2) ^ a) ^ (1 - a / (a + g)) * C ^ (a / (a + g)) *
        r ^ (κ * (a / (a + g))) := by
  set θ := a / (a + g) with hθ
  have hag : a + g ≠ 0 := by linarith
  have hd0 : 0 ≤ d := hd.le
  have h32 : (0 : ℝ) ≤ 3 / 2 := by norm_num
  have h3a : 0 ≤ A * (3 / 2) ^ a := mul_nonneg hA (Real.rpow_nonneg h32 _)
  have e1 : (A * (3 / 2 * d) ^ a) ^ (1 - θ) =
      (A * (3 / 2) ^ a) ^ (1 - θ) * d ^ (a * (1 - θ)) := by
    rw [Real.mul_rpow h32 hd0, ← mul_assoc, Real.mul_rpow h3a (Real.rpow_nonneg hd0 _),
      ← Real.rpow_mul hd0]
  have e2 : (C * d ^ (-g) * r ^ κ) ^ θ = C ^ θ * d ^ (-g * θ) * r ^ (κ * θ) := by
    rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hd0 _)) (Real.rpow_nonneg hr _),
      Real.mul_rpow hC (Real.rpow_nonneg hd0 _), ← Real.rpow_mul hd0, ← Real.rpow_mul hr]
  have h1 : (a + g) * θ = a := by
    rw [hθ]
    field_simp
  have hexp : a * (1 - θ) + -g * θ = 0 := by
    linear_combination (-1 : ℝ) * h1
  have hdd : d ^ (a * (1 - θ)) * d ^ (-g * θ) = 1 := by
    rw [← Real.rpow_add hd, hexp, Real.rpow_zero]
  rw [e1, e2]
  calc (A * (3 / 2) ^ a) ^ (1 - θ) * d ^ (a * (1 - θ)) *
        (C ^ θ * d ^ (-g * θ) * r ^ (κ * θ))
      = (A * (3 / 2) ^ a) ^ (1 - θ) * C ^ θ * r ^ (κ * θ) *
          (d ^ (a * (1 - θ)) * d ^ (-g * θ)) := by ring
    _ = (A * (3 / 2) ^ a) ^ (1 - θ) * C ^ θ * r ^ (κ * θ) := by rw [hdd, mul_one]

/-- The interpolated exponent `min a (κ a / (a + g))` is positive. -/
theorem min_exponent_offOrigin_pos {a g κ : ℝ} (ha : 0 < a) (hg : 0 ≤ g) (hκ : 0 < κ) :
    0 < min a (κ * (a / (a + g))) :=
  lt_min ha (mul_pos hκ (div_pos ha (by linarith)))

/-- **Annular interpolation of ball power bounds.** An origin bound
`v (ball 0 s) ≤ A s ^ a` for `0 < s ≤ max 3 (3 R / 2)` and an off-origin bound
`v (ball z r) ≤ C ‖z‖ ^ (-g) r ^ κ` for `2 r < ‖z‖ ≤ R`, `r ≤ 1`, give a uniform
power bound for all balls `ball z r` with `‖z‖ ≤ R` and `0 < r ≤ 1`. -/
theorem ball_le_ofReal_rpow_of_origin_of_offOrigin
    {E : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] (v : Measure E)
    {R A C a g κ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : 0 < a) (hg : 0 ≤ g)
    (horig : ∀ s : ℝ, 0 < s → s ≤ max 3 (3 / 2 * R) →
      v (ball 0 s) ≤ ENNReal.ofReal (A * s ^ a))
    (hoff : ∀ z : E, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 → 2 * r < ‖z‖ →
      v (ball z r) ≤ ENNReal.ofReal (C * ‖z‖ ^ (-g) * r ^ κ)) :
    ∀ z : E, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      v (ball z r) ≤ ENNReal.ofReal
        (max (A * 3 ^ a) ((A * (3 / 2) ^ a) ^ (1 - a / (a + g)) * C ^ (a / (a + g))) *
          r ^ min a (κ * (a / (a + g)))) := by
  intro z hz r hr0 hr1
  have hag : 0 < a + g := by linarith
  have hθ0 : 0 ≤ a / (a + g) := div_nonneg ha.le hag.le
  have hθ1 : a / (a + g) ≤ 1 := (div_le_one hag).2 (by linarith)
  have hK1 : 0 ≤ A * 3 ^ a := mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)
  by_cases hnear : ‖z‖ ≤ 2 * r
  · have hsub : ball z r ⊆ ball (0 : E) (3 * r) := by
      intro x hx
      rw [mem_ball, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      have := norm_sub_norm_le x z
      linarith
    calc v (ball z r) ≤ v (ball 0 (3 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (A * (3 * r) ^ a) :=
          horig _ (by linarith) (le_trans (by linarith) (le_max_left _ _))
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.mul_rpow (by norm_num) hr0.le, ← mul_assoc]
          exact mul_le_mul (le_max_left _ _)
            (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (min_le_left _ _))
            (Real.rpow_nonneg hr0.le _) (le_trans hK1 (le_max_left _ _))
  · replace hnear : 2 * r < ‖z‖ := not_le.mp hnear
    have hd : 0 < ‖z‖ := lt_trans (by linarith) hnear
    have hsub : ball z r ⊆ ball (0 : E) (3 / 2 * ‖z‖) := by
      intro x hx
      rw [mem_ball, dist_eq_norm] at hx
      rw [mem_ball_zero_iff]
      have := norm_sub_norm_le x z
      linarith
    have h1 : v (ball z r) ≤ ENNReal.ofReal (A * (3 / 2 * ‖z‖) ^ a) :=
      (measure_mono hsub).trans
        (horig _ (by positivity) (le_trans (by linarith) (le_max_right _ _)))
    have h2 := hoff z hz r hr0 hr1 hnear
    have hX : 0 ≤ A * (3 / 2 * ‖z‖) ^ a := by positivity
    have hY : 0 ≤ C * ‖z‖ ^ (-g) * r ^ κ := by positivity
    have hmin : v (ball z r) ≤
        ENNReal.ofReal (min (A * (3 / 2 * ‖z‖) ^ a) (C * ‖z‖ ^ (-g) * r ^ κ)) := by
      rcases min_cases (A * (3 / 2 * ‖z‖) ^ a) (C * ‖z‖ ^ (-g) * r ^ κ) with
        ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> assumption
    refine hmin.trans (ENNReal.ofReal_le_ofReal ?_)
    calc min (A * (3 / 2 * ‖z‖) ^ a) (C * ‖z‖ ^ (-g) * r ^ κ)
        ≤ (A * (3 / 2 * ‖z‖) ^ a) ^ (1 - a / (a + g)) *
            (C * ‖z‖ ^ (-g) * r ^ κ) ^ (a / (a + g)) :=
          min_le_rpow_mul_rpow hX hY hθ0 hθ1
      _ = (A * (3 / 2) ^ a) ^ (1 - a / (a + g)) * C ^ (a / (a + g)) *
            r ^ (κ * (a / (a + g))) :=
          rpow_mul_rpow_offOrigin_eq hA hC ha hg hd hr0.le
      _ ≤ _ := mul_le_mul (le_max_right _ _)
            (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (min_le_right _ _))
            (Real.rpow_nonneg hr0.le _) (le_trans hK1 (le_max_left _ _))

end LatticeProb.LQG

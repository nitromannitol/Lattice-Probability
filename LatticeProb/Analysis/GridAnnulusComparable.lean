import LatticeProb.Analysis.GridAnnulusCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Grid annuli comparable to a given annulus

Let `B_r(z) \ B̄_s(z)` be an annulus with `r ≥ 3 s`, and approximate it, as in
`LatticeProb.exists_grid_annulus_approx`, by an annulus `B_{r'}(z') \ B̄_{s'}(z')` with `z'` in the lattice `η ℤ²`,
`|z - z'| ≤ η` and radii in a geometric grid of ratio `q`, so that `(r - η) / q < r' ≤ r - η` and
`s + η ≤ s' < q (s + η)`. If the grid is fine, `q ^ 2 ≤ 29 / 20` (for instance `q = 2 ^ (1 / 4)`), and the lattice
spacing is small compared to the inner radius, `η ≤ s / 100`, then the grid annulus is comparable to the given one:
`s' ≤ r' / 2`, `r' ∈ [r / 2, r]`, `s' ∈ [s, 2 s]` and `log (r / s) ≤ 2 log (r' / s')`. A dyadic grid (`q = 2`) does not
suffice for the first of these when `r / s` is close to `3`.

## Main results

* `LatticeProb.grid_annulus_comparable`: the comparison of the radii, for given grid radii.
* `LatticeProb.div_log_le_two_mul_div_log`: the resulting comparison `C / log (r' / s') ≤ 2 C / log (r / s)`.
* `LatticeProb.exists_grid_annulus_comparable_mem`: a comparable grid annulus with parameters in
  `LatticeProb.gridAnnulusIndex`, for centres `|z| ≤ ρ`, outer radii in `[2 x₁, y₁]` and inner radii in `[x₂, y₂ / 2]`.
* `LatticeProb.one_lt_two_rpow_quarter`, `LatticeProb.two_rpow_quarter_sq_le`: the ratio `q = 2 ^ (1 / 4)` is
  admissible.
-/

open Metric Set

namespace LatticeProb

/-- Comparison of a grid annulus with the annulus it approximates. If `1 < q`, `q ^ 2 ≤ 29 / 20`, `0 < η ≤ s / 100`,
`3 s ≤ r`, `(r - η) / q < r' ≤ r - η` and `s + η ≤ s' < q (s + η)`, then `s' ≤ r' / 2`, `r / 2 ≤ r' ≤ r`,
`s ≤ s' ≤ 2 s` and `log (r / s) ≤ 2 log (r' / s')`. -/
theorem grid_annulus_comparable {q η r s r' s' : ℝ} (hq : 1 < q) (hq2 : q ^ 2 ≤ 29 / 20) (hη : 0 < η)
    (hηs : η ≤ s / 100) (hrs : 3 * s ≤ r) (hr'₁ : (r - η) / q < r') (hr'₂ : r' ≤ r - η)
    (hs'₁ : s + η ≤ s') (hs'₂ : s' < q * (s + η)) :
    s' ≤ r' / 2 ∧ r / 2 ≤ r' ∧ r' ≤ r ∧ s ≤ s' ∧ s' ≤ 2 * s ∧
      Real.log (r / s) ≤ 2 * Real.log (r' / s') := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < s := by linarith
  have hr : 0 < r := by linarith
  have hsη : 0 < s + η := by linarith
  have hs' : 0 < s' := by linarith
  have hq121 : q ≤ 121 / 100 := by nlinarith
  have hqr' : r - η < q * r' := by
    rw [div_lt_iff₀ hq0] at hr'₁
    linarith
  have e1 : 2 * q ^ 2 * (s + η) ≤ r - η := by
    nlinarith [mul_le_mul_of_nonneg_right hq2 hsη.le]
  have e2 : q * r ≤ 2 * (r - η) := by
    nlinarith [mul_le_mul_of_nonneg_right hq121 hr.le]
  have e3 : 2 * r * q ^ 2 * (s + η) ≤ 3 * s * (r - η) := by
    nlinarith [mul_le_mul_of_nonneg_left hq2 (mul_pos hr hsη).le, mul_le_mul_of_nonneg_left hηs hr.le,
      mul_le_mul_of_nonneg_left hηs hs.le, mul_le_mul_of_nonneg_left hrs hs.le]
  refine ⟨?_, ?_, by linarith, by linarith, ?_, ?_⟩
  · have h : q * (2 * s') ≤ q * r' := by nlinarith [mul_lt_mul_of_pos_left hs'₂ hq0]
    have := le_of_mul_le_mul_left h hq0
    linarith
  · have h : q * r ≤ q * (2 * r') := by nlinarith
    have := le_of_mul_le_mul_left h hq0
    linarith
  · nlinarith [mul_le_mul_of_nonneg_right hq121 hsη.le]
  · have h3 : q * (2 * r * s') ≤ q * (3 * s * r') := by
      nlinarith [mul_lt_mul_of_pos_left hs'₂ (by positivity : (0 : ℝ) < 2 * r * q),
        mul_lt_mul_of_pos_left hqr' (by positivity : (0 : ℝ) < 3 * s)]
    have h3' := le_of_mul_le_mul_left h3 hq0
    have hx : 3 ≤ r / s := by
      rw [le_div_iff₀ hs]
      linarith
    have hy : 2 / 3 * (r / s) ≤ r' / s' := by
      rw [mul_div_assoc', div_le_div_iff₀ hs hs']
      nlinarith
    have hsq : r / s ≤ (r' / s') ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hy 2
      nlinarith
    calc Real.log (r / s) ≤ Real.log ((r' / s') ^ 2) := Real.log_le_log (by positivity) hsq
      _ = 2 * Real.log (r' / s') := by rw [Real.log_pow]; norm_num

/-- If `log x ≤ 2 log y` and `x > 1`, then `C / log y ≤ 2 C / log x` for `C ≥ 0`. -/
theorem div_log_le_two_mul_div_log {x y C : ℝ} (hx : 1 < x) (hxy : Real.log x ≤ 2 * Real.log y)
    (hC : 0 ≤ C) : C / Real.log y ≤ 2 * C / Real.log x := by
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hly : 0 < Real.log y := by linarith
  rw [div_le_div_iff₀ hly hlx]
  nlinarith [mul_le_mul_of_nonneg_left hxy hC]

/-- A comparable grid annulus with parameters in `gridAnnulusIndex`. Let `1 < q`, `q ^ 2 ≤ 29 / 20`, `|z| ≤ ρ`,
`0 < η ≤ s / 100`, `3 s ≤ r`, `0 < x₁ ≤ r / 2`, `r ≤ y₁`, `0 < x₂ ≤ s` and `2 s ≤ y₂`. Then there is a grid parameter
`(m, n, a, b) ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂` with `z' = η (m + n i)` within `η` of `z`, `B_{q^a}(z') ⊆ B_r(z)`,
`B̄_s(z) ⊆ B̄_{q^b}(z')`, `B_s(z) ⊆ B_{q^b}(z')`, `q ^ b ≤ q ^ a / 2`, `r / 2 ≤ q ^ a ≤ r`, `s ≤ q ^ b ≤ 2 s` and
`log (r / s) ≤ 2 log (q ^ a / q ^ b)`. -/
theorem exists_grid_annulus_comparable_mem {q η ρ x₁ y₁ x₂ y₂ : ℝ} (hq : 1 < q) (hq2 : q ^ 2 ≤ 29 / 20)
    (hη : 0 < η) {z : ℂ} (hz : ‖z‖ ≤ ρ) {s r : ℝ} (hηs : η ≤ s / 100) (hrs : 3 * s ≤ r)
    (hx₁ : 0 < x₁) (hx₁r : x₁ ≤ r / 2) (hy₁ : r ≤ y₁) (hx₂ : 0 < x₂) (hx₂s : x₂ ≤ s)
    (hy₂ : 2 * s ≤ y₂) :
    ∃ i ∈ gridAnnulusIndex q η ρ x₁ y₁ x₂ y₂,
      ‖z - (η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)‖ ≤ η ∧
      ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.1) ⊆ ball z r ∧
      closedBall z s ⊆ closedBall ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2) ∧
      ball z s ⊆ ball ((η : ℂ) * ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I)) (q ^ i.2.2.2) ∧
      q ^ i.2.2.2 ≤ q ^ i.2.2.1 / 2 ∧ r / 2 ≤ q ^ i.2.2.1 ∧ q ^ i.2.2.1 ≤ r ∧
      s ≤ q ^ i.2.2.2 ∧ q ^ i.2.2.2 ≤ 2 * s ∧
      Real.log (r / s) ≤ 2 * Real.log (q ^ i.2.2.1 / q ^ i.2.2.2) := by
  have hq0 : 0 < q := by linarith
  have hs : 0 < s := by linarith
  have hr : η < r := by linarith
  have hq121 : q ≤ 121 / 100 := by nlinarith
  have hA : r / 2 ≤ (r - η) / q := by
    rw [le_div_iff₀ hq0]
    nlinarith [mul_le_mul_of_nonneg_left hq121 (by linarith : (0 : ℝ) ≤ r)]
  have hB : q * (s + η) ≤ 2 * s := by
    nlinarith [mul_le_mul_of_nonneg_right hq121 (by linarith : (0 : ℝ) ≤ s + η)]
  obtain ⟨i, hi, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_grid_annulus_approx_mem hq hη hz hs.le hr hx₁ (hx₁r.trans hA) (by linarith : r - η ≤ y₁) hx₂
      (by linarith : x₂ ≤ s + η) (hB.trans hy₂)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := grid_annulus_comparable hq hq2 hη hηs hrs h5 h6 h7 h8
  exact ⟨i, hi, h1, h2, h3, h4, c1, c2, c3, c4, c5, c6⟩

/-- The ratio `q = 2 ^ (1 / 4)` exceeds `1`. -/
theorem one_lt_two_rpow_quarter : 1 < (2 : ℝ) ^ (1 / 4 : ℝ) :=
  Real.one_lt_rpow (by norm_num) (by norm_num)

/-- The ratio `q = 2 ^ (1 / 4)` satisfies `q ^ 2 ≤ 29 / 20`. -/
theorem two_rpow_quarter_sq_le : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 ≤ 29 / 20 := by
  have h4 : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hpos : 0 < (2 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  nlinarith [sq_nonneg (((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 - 29 / 20)]

end LatticeProb

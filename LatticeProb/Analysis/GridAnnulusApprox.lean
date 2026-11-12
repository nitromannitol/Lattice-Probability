import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Round

/-!
# Approximating annuli by annuli with grid parameters

Union bounds over all annuli `B_r(z) \ B̄_s(z)` are usually reduced to a finite family: centers in the lattice
`η ℤ²` and radii in a geometric grid `{q ^ n : n ∈ ℤ}` with ratio `q > 1`. Every annulus contains, up to the
inner disc, an annulus with grid parameters whose inner disc contains `B̄_s(z)`, whose outer disc lies in `B_r(z)`
and whose radii are comparable to `r - η` and `s + η`.

## Main results

* `LatticeProb.exists_lattice_point_norm_sub_le`: every `z ∈ ℂ` is within `η` of a point of `η (ℤ + ℤ i)`.
* `LatticeProb.exists_zpow_lt_le`, `LatticeProb.exists_le_zpow_lt`: for `q > 1` and `x > 0` there are
  `q ^ a ∈ (x / q, x]` and `q ^ b ∈ [x, q x)`.
* `LatticeProb.exists_grid_annulus_approx`: for `q > 1`, `η > 0`, `0 ≤ s` and `η < r`, there are a lattice point
  `z' = η (m + n i)` with `|z - z'| ≤ η` and integers `a, b` with `B_{q^a}(z') ⊆ B_r(z)`, `B̄_s(z) ⊆ B̄_{q^b}(z')`,
  `B_s(z) ⊆ B_{q^b}(z')`, `(r - η) / q < q ^ a ≤ r - η` and `s + η ≤ q ^ b < q (s + η)`.
-/

open Metric Set

namespace LatticeProb

/-- Every `z ∈ ℂ` lies within distance `η` of a point of the lattice `η (ℤ + ℤ i)`, for `η > 0`. -/
theorem exists_lattice_point_norm_sub_le {η : ℝ} (hη : 0 < η) (z : ℂ) :
    ∃ m n : ℤ, ‖z - (η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)‖ ≤ η := by
  refine ⟨round (z.re / η), round (z.im / η), ?_⟩
  set w := z - (η : ℂ) * ((round (z.re / η) : ℂ) + (round (z.im / η) : ℂ) * Complex.I) with hw
  have hre : w.re = η * (z.re / η - round (z.re / η)) := by
    rw [hw]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  have him : w.im = η * (z.im / η - round (z.im / η)) := by
    rw [hw]
    simp only [Complex.sub_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    field_simp
    ring
  have h1 : |w.re| ≤ η / 2 := by
    rw [hre, abs_mul, abs_of_pos hη]
    have := abs_sub_round (z.re / η)
    nlinarith
  have h2 : |w.im| ≤ η / 2 := by
    rw [him, abs_mul, abs_of_pos hη]
    have := abs_sub_round (z.im / η)
    nlinarith
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ ≤ η := by linarith

/-- For `q > 1` and `x > 0` there is an integer power `q ^ a ∈ (x / q, x]`. -/
theorem exists_zpow_lt_le {q x : ℝ} (hq : 1 < q) (hx : 0 < x) : ∃ a : ℤ, x / q < q ^ a ∧ q ^ a ≤ x := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hx hq
  refine ⟨n, ?_, hn1⟩
  rw [zpow_add_one₀ (by positivity : q ≠ 0)] at hn2
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < q)]
  exact hn2

/-- For `q > 1` and `x > 0` there is an integer power `q ^ b ∈ [x, q x)`. -/
theorem exists_le_zpow_lt {q x : ℝ} (hq : 1 < q) (hx : 0 < x) : ∃ b : ℤ, x ≤ q ^ b ∧ q ^ b < q * x := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hx hq
  refine ⟨n + 1, hn2, ?_⟩
  rw [zpow_add_one₀ (by positivity : q ≠ 0), mul_comm]
  exact mul_lt_mul_of_pos_left hn1 (by positivity)

/-- **Grid approximation of annuli.** For `q > 1`, `η > 0`, `0 ≤ s` and `η < r`, there are a lattice point
`z' = η (m + n i)` with `|z - z'| ≤ η` and integers `a, b` such that `B_{q^a}(z') ⊆ B_r(z)`,
`B̄_s(z) ⊆ B̄_{q^b}(z')`, `B_s(z) ⊆ B_{q^b}(z')`, `(r - η) / q < q ^ a ≤ r - η` and `s + η ≤ q ^ b < q (s + η)`. -/
theorem exists_grid_annulus_approx {q η : ℝ} (hq : 1 < q) (hη : 0 < η) (z : ℂ) {s r : ℝ} (hs : 0 ≤ s)
    (hr : η < r) :
    ∃ m n a b : ℤ,
      ‖z - (η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)‖ ≤ η ∧
      ball ((η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (q ^ a) ⊆ ball z r ∧
      closedBall z s ⊆ closedBall ((η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (q ^ b) ∧
      ball z s ⊆ ball ((η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (q ^ b) ∧
      (r - η) / q < q ^ a ∧ q ^ a ≤ r - η ∧ s + η ≤ q ^ b ∧ q ^ b < q * (s + η) := by
  obtain ⟨m, n, hmn⟩ := exists_lattice_point_norm_sub_le hη z
  obtain ⟨a, ha1, ha2⟩ := exists_zpow_lt_le hq (sub_pos.2 hr)
  obtain ⟨b, hb1, hb2⟩ := exists_le_zpow_lt hq (by linarith : 0 < s + η)
  set z' : ℂ := (η : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)
  have hd : dist z z' ≤ η := by rw [dist_eq_norm]; exact hmn
  have hd' : dist z' z ≤ η := by rw [dist_comm]; exact hd
  refine ⟨m, n, a, b, hmn, ?_, ?_, ?_, ha1, ha2, hb1, hb2⟩
  · exact ball_subset_ball' (by linarith)
  · exact closedBall_subset_closedBall' (by linarith)
  · exact ball_subset_ball' (by linarith)

end LatticeProb

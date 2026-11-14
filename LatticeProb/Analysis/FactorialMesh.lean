import Mathlib

/-!
# Factorial-power grids

Factorial-power meshes converge to zero, and the corresponding finite grids
are nested. These properties hold for every positive natural exponent.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace LatticeProb

/-- A reciprocal factorial-power mesh tends to zero for a positive exponent. -/
theorem tendsto_one_div_factorial_pow (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => 1 / ((n.factorial : ℝ) ^ p)) atTop (𝓝 0) := by
  have hfact : Tendsto (fun n : ℕ => (n.factorial : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
  have hrec : Tendsto (fun n : ℕ => (n.factorial : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hfact
  simpa only [one_div, inv_pow, zero_pow (Nat.ne_of_gt hp)] using hrec.pow p

/-- Factorial-power grid denominators divide all later denominators. -/
theorem factorial_pow_dvd_factorial_pow {n m : ℕ} (h : n ≤ m) (p : ℕ) :
    n.factorial ^ p ∣ m.factorial ^ p :=
  pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial h) p

/-- Every point of a factorial-power grid belongs to each later grid. -/
theorem factorial_grid_nested {n m p : ℕ} (h : n ≤ m)
    (i : Fin (n.factorial ^ p)) :
    ∃ j : Fin (m.factorial ^ p),
      (i.val : ℝ) / (n.factorial ^ p : ℕ) =
        (j.val : ℝ) / (m.factorial ^ p : ℕ) := by
  obtain ⟨k, hk⟩ := factorial_pow_dvd_factorial_pow h p
  have hn : 0 < n.factorial ^ p := pow_pos (Nat.factorial_pos n) _
  have hm : 0 < m.factorial ^ p := pow_pos (Nat.factorial_pos m) _
  have hkpos : 0 < k := by
    rw [hk] at hm
    exact Nat.pos_of_mul_pos_left hm
  refine ⟨⟨i.val * k, ?_⟩, ?_⟩
  · rw [hk]
    exact Nat.mul_lt_mul_of_pos_right i.isLt hkpos
  · change (i.val : ℝ) / (n.factorial ^ p : ℕ) =
      ((i.val * k : ℕ) : ℝ) / (m.factorial ^ p : ℕ)
    rw [hk, Nat.cast_mul, Nat.cast_mul]
    have hn' : (n.factorial ^ p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    field_simp

end LatticeProb

import LatticeProb.Lattice.Planar.TriangleCount

/-!
# The area normalization of the planar l1 triangle

Exact parity counts bound the real cardinality between the quadratic area and
that area plus a linear boundary term. All ratio estimates use positive radii.
-/

namespace LatticeProb.Lattice.Planar

open Filter
open scoped Topology

/-- The real cardinality differs from the triangular area by at most `L + 1`. -/
theorem card_triangle_real_bounds (L : ℕ) :
    (L : ℝ) ^ 2 / 2 ≤ ((triangle L).card : ℝ) ∧
      ((triangle L).card : ℝ) ≤ (L : ℝ) ^ 2 / 2 + L + 1 := by
  have hrem := Nat.mod_lt L (by omega : 0 < 2)
  have hdiv := Nat.mod_add_div L 2
  rcases (show L % 2 = 0 ∨ L % 2 = 1 by omega) with he | ho
  · have hL : L = 2 * (L / 2) := by omega
    rw [hL, card_triangle_even]
    push_cast
    constructor <;> nlinarith [sq_nonneg (L / 2 : ℝ)]
  · have hL : L = 2 * (L / 2) + 1 := by omega
    rw [hL, card_triangle_odd]
    push_cast
    have hnonneg : (0 : ℝ) ≤ (L / 2 : ℕ) := Nat.cast_nonneg _
    constructor <;> nlinarith

/-- Positive radii give the area coefficient with an explicit vanishing error bound. -/
theorem card_triangle_ratio_bounds (L : ℕ) (hL : 0 < L) :
    (1 / 2 : ℝ) ≤ ((triangle L).card : ℝ) / (L : ℝ) ^ 2 ∧
      ((triangle L).card : ℝ) / (L : ℝ) ^ 2 ≤
        1 / 2 + 1 / (L : ℝ) + (1 / (L : ℝ)) ^ 2 := by
  have hpos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hsq : (0 : ℝ) < (L : ℝ) ^ 2 := sq_pos_of_pos hpos
  obtain ⟨hlo, hhi⟩ := card_triangle_real_bounds L
  constructor
  · apply (le_div_iff₀ hsq).mpr
    nlinarith
  · apply (div_le_iff₀ hsq).mpr
    have heq : (1 / 2 + 1 / (L : ℝ) + (1 / (L : ℝ)) ^ 2) * (L : ℝ) ^ 2 =
        (L : ℝ) ^ 2 / 2 + L + 1 := by
      field_simp [ne_of_gt hpos]
    rw [heq]
    exact hhi

/-- The literal real ratio tends to one half; the estimates only use the tail `L ≥ 1`. -/
theorem tendsto_card_triangle_div_sq :
    Tendsto (fun L : ℕ => ((triangle L).card : ℝ) / (L : ℝ) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hinv : Tendsto (fun L : ℕ => 1 / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hu : Tendsto (fun L : ℕ => 1 / 2 + 1 / (L : ℝ) + (1 / (L : ℝ)) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [zero_pow (by omega : 2 ≠ 0), add_zero] using
      (tendsto_const_nhds.add hinv).add (hinv.pow 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 1] with L hL
    exact (card_triangle_ratio_bounds L (by omega)).1
  · filter_upwards [eventually_ge_atTop 1] with L hL
    exact (card_triangle_ratio_bounds L (by omega)).2

/-- A spatially constant density inherits the triangle's one-half normalization. -/
theorem tendsto_constant_density_triangle (a : ℝ) :
    Tendsto (fun L : ℕ => (∑ _z ∈ triangle L, a) / (L : ℝ) ^ 2)
      atTop (𝓝 (a / 2)) := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_div_assoc, mul_comm,
    mul_one_div] using tendsto_card_triangle_div_sq.const_mul a

end LatticeProb.Lattice.Planar

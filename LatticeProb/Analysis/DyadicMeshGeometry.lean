import Mathlib

/-!
# Dyadic mesh and unit-disc geometry for grid sums

Elementary facts about the dyadic grid of mesh `4 / 2 ^ k` on `[-2, 2)` and about balls in the complex plane:
positivity of the mesh, the relation between `16 / 4 ^ k` and the square of the mesh, the floor bound
`⌊(t + 2) / (4 / 2 ^ k)⌋₊ < 2 ^ k` for `t ∈ [-2, 2)`, the distance from a point of the open unit disc to the
complement of a subset of that disc, the inclusion of a closed disc into the open unit disc, and continuity of
a slice of a function that is continuous on `(0, ∞) × ℂ`. None of these uses a literature result.
-/

open Metric Set Filter Topology

namespace LatticeProb.DyadicMeshGeometry

/-- The dyadic mesh `4 / 2 ^ k` is strictly positive. -/
lemma mesh_pos (k : ℕ) : (0 : ℝ) < 4 / 2 ^ k := by positivity

/-- The area factor `16 / 4 ^ k` of a dyadic cell equals the product of the two side lengths `4 / 2 ^ k`,
as extended nonnegative reals. -/
lemma ofReal_sixteen (k : ℕ) :
    ENNReal.ofReal (16 / 4 ^ k) = ENNReal.ofReal (4 / 2 ^ k) * ENNReal.ofReal (4 / 2 ^ k) := by
  rw [← ENNReal.ofReal_mul (mesh_pos k).le]
  congr 1
  rw [div_mul_div_comm, ← mul_pow]
  norm_num

/-- For `t ∈ [-2, 2)`, the floor of `(t + 2) / (4 / 2 ^ k)` is strictly less than `2 ^ k`. -/
lemma lt_two_pow_of_floor {k : ℕ} {t : ℝ} (ht : t < 2) (ht' : -2 ≤ t) :
    ⌊(t + 2) / (4 / 2 ^ k)⌋₊ < 2 ^ k := by
  have hh := mesh_pos k
  have hx : (0 : ℝ) ≤ (t + 2) / (4 / 2 ^ k) := div_nonneg (by linarith) hh.le
  rw [Nat.floor_lt hx, div_lt_iff₀ hh]
  have h4 : (2 : ℝ) ^ k * (4 / 2 ^ k) = 4 := by field_simp
  push_cast
  linarith [h4]

/-- If `U` lies in the open unit disc and `‖z‖ < 1`, the distance from `z` to the complement of `U` is at most
`1 - ‖z‖`. The point `z / ‖z‖` (or any unit vector, when `z = 0`) lies outside `U`. -/
lemma infDist_compl_le_one_sub_norm {U : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1) {z : ℂ} (hz : ‖z‖ < 1) :
    infDist z Uᶜ ≤ 1 - ‖z‖ := by
  have hw : ∀ w : ℂ, 1 ≤ ‖w‖ → infDist z Uᶜ ≤ dist z w := by
    intro w hw1
    apply infDist_le_dist_of_mem
    rw [Set.mem_compl_iff]
    intro hwU
    have h2 := mem_ball_zero_iff.mp (hUsub hwU)
    linarith
  rcases eq_or_ne z 0 with h0 | h0
  · subst h0
    have h1 := hw 1 (by simp)
    simpa using h1
  · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr h0
    have hnorm : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    have hdist : dist z ((‖z‖⁻¹ : ℝ) • z) ≤ 1 - ‖z‖ := by
      rw [dist_eq_norm, show z - (‖z‖⁻¹ : ℝ) • z = (1 - ‖z‖⁻¹ : ℝ) • z by
        rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
      have hinv : 1 < ‖z‖⁻¹ := (one_lt_inv₀ hpos).mpr hz
      rw [abs_of_neg (show 1 - ‖z‖⁻¹ < 0 by linarith)]
      have key : -(1 - ‖z‖⁻¹) * ‖z‖ = 1 - ‖z‖ := by
        rw [neg_mul, sub_mul, inv_mul_cancel₀ hpos.ne']
        ring
      exact key.le
    exact (hw _ hnorm.ge).trans hdist

/-- A closed disc of radius `r` centred at `z` lies in the open unit disc when `r + ‖z‖ < 1`. -/
lemma closedBall_subset_ball_of_add_norm_lt {r : ℝ} {z : ℂ} (h : r + ‖z‖ < 1) :
    closedBall z r ⊆ ball (0 : ℂ) 1 := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  rw [mem_ball_zero_iff]
  have h1 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
  linarith

/-- If `c` is continuous on `(0, ∞) × ℂ`, then for every `r > 0` the slice `z ↦ c r z` is continuous. -/
lemma slice_continuous_of_continuousOn {c : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => c p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ∀ r : ℝ, 0 < r → Continuous fun z => c r z := by
  intro r hr
  have h1 : Continuous fun z : ℂ => ((r, z) : ℝ × ℂ) := continuous_const.prodMk continuous_id
  exact hcont.comp_continuous h1 (fun z => ⟨hr, mem_univ z⟩)

end LatticeProb.DyadicMeshGeometry

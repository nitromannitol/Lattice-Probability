/-
# Endpoint segments inside the original continuum neighborhoods

Positive separation of the original compact sets determines an inward scaling
close to one. Each radial endpoint segment then stays in its original set's
neighborhood. The disk is specified by coordinate squares; metric neighborhoods
use the ambient product metric.
-/
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring



open Metric Set

namespace LatticeProb.Topology

/-- The coordinate disk is contained in the ambient product unit ball. -/
theorem norm_le_one_of_mem_coordinate_disk {z : ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1) : ‖z‖ ≤ 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have hx : z.1 ^ 2 ≤ 1 := (le_add_of_nonneg_right (sq_nonneg z.2)).trans hz
  have hy : z.2 ^ 2 ≤ 1 := (le_add_of_nonneg_left (sq_nonneg z.1)).trans hz
  exact max_le ((sq_le_one_iff_abs_le_one z.1).mp hx)
    ((sq_le_one_iff_abs_le_one z.2).mp hy)

/-- Moving a disk point radially by `1 - t` changes it by at most that amount. -/
theorem dist_smul_self_le_one_sub {z : ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1) {t : ℝ} (ht : t ≤ 1) :
    dist (t • z) z ≤ 1 - t := by
  rw [dist_eq_norm, show t • z - z = (t - 1) • z by rw [sub_smul, one_smul],
    norm_smul, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr ht)]
  calc
    -(t - 1) * ‖z‖ ≤ -(t - 1) * 1 :=
      mul_le_mul_of_nonneg_left (norm_le_one_of_mem_coordinate_disk hz) (by linarith)
    _ = 1 - t := by ring

/-- A radial segment consists of scaled copies with factors between its endpoint factors. -/
theorem mem_segment_self_smul_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z : E) {ρ : ℝ} (hρ : ρ ≤ 1) {w : E} :
    w ∈ segment ℝ z (ρ • z) ↔ ∃ t ∈ Icc ρ 1, w = t • z := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a + b * ρ, ⟨?_, ?_⟩, ?_⟩
    · calc
        ρ = a * ρ + b * ρ := by rw [← add_mul, hab, one_mul]
        _ ≤ a + b * ρ := add_le_add (mul_le_of_le_one_right ha hρ) le_rfl
    · calc
        a + b * ρ ≤ a + b := add_le_add le_rfl (mul_le_of_le_one_right hb hρ)
        _ = 1 := hab
    · rw [add_smul, mul_smul]
  · rintro ⟨t, ⟨hρt, ht⟩, rfl⟩
    by_cases heq : ρ = 1
    · have ht1 : t = 1 := le_antisymm ht (heq ▸ hρt)
      rw [ht1, one_smul]
      exact left_mem_segment ℝ z (ρ • z)
    · have hpos : 0 < 1 - ρ := sub_pos.mpr (lt_of_le_of_ne hρ heq)
      refine ⟨(t - ρ) / (1 - ρ), (1 - t) / (1 - ρ),
        div_nonneg (sub_nonneg.mpr hρt) hpos.le,
        div_nonneg (sub_nonneg.mpr ht) hpos.le, ?_, ?_⟩
      · field_simp
        ring
      · rw [smul_smul, ← add_smul]
        congr 1
        field_simp
        ring

/-- A short inward radial segment remains in a neighborhood of the original set. -/
theorem segment_self_smul_subset_thickening {K : Set (ℝ × ℝ)} {z : ℝ × ℝ}
    (hz : z ∈ K) (hzd : z.1 ^ 2 + z.2 ^ 2 ≤ 1) {ρ δ : ℝ}
    (hρ : ρ ≤ 1) (hδ : 1 - ρ < δ) :
    segment ℝ z (ρ • z) ⊆ thickening δ K := by
  intro w hw
  obtain ⟨t, ⟨hρt, ht⟩, rfl⟩ := (mem_segment_self_smul_iff z hρ).mp hw
  exact mem_thickening_iff.mpr ⟨z, hz,
    (dist_smul_self_le_one_sub hzd ht).trans_lt (by linarith)⟩

/-- **Radial endpoints in separated neighborhoods.** Separation of the original compact disk sets supplies one scaling factor and
disjoint original neighborhoods containing every corresponding radial segment. -/
theorem exists_scaling_in_original_thickenings {K L : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L)
    (hKd : K ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1})
    (hLd : L ⊆ {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}) :
    ∃ δ > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 - ρ < δ ∧
      Disjoint (thickening δ K) (thickening δ L) ∧
      (∀ z ∈ K, segment ℝ z (ρ • z) ⊆ thickening δ K) ∧
      (∀ z ∈ L, segment ℝ z (ρ • z) ⊆ thickening δ L) := by
  obtain ⟨δ, hδ, hsep⟩ := hKL.exists_thickenings hK hL.isClosed
  let η := min (δ / 2) (1 / 2 : ℝ)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  have hρ0 : 0 < 1 - η := by linarith
  have hρ1 : 1 - η < 1 := by linarith
  have hshort : 1 - (1 - η) < δ := by linarith
  refine ⟨δ, hδ, 1 - η, hρ0, hρ1, hshort, hsep, ?_, ?_⟩
  · intro z hz
    exact segment_self_smul_subset_thickening hz (hKd hz) hρ1.le hshort
  · intro z hz
    exact segment_self_smul_subset_thickening hz (hLd hz) hρ1.le hshort

end LatticeProb.Topology

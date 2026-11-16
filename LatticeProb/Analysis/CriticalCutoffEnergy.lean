import LatticeProb.Euclidean.Summability
import LatticeProb.Euclidean.Estimates

/-!
# Critical lattice cutoff energy

Estimates for the critical Euclidean jump kernel on the integer lattice.
-/

noncomputable section

open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Summability
open LatticeProb.Euclidean.Estimates LatticeProb.Euclidean.Shell
open LatticeProb.Euclidean.Series

namespace LatticeProb.Analysis.CriticalCutoffEnergy

/-- The critical kernel is summable on the punctured lattice. -/
theorem summable_kernel (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun z : {z : Site d // z ≠ 0} =>
      (radius (physical 1 z.val) ^ (d + 2))⁻¹) := by
  apply (nonzero_radial_error_summable_real d hd).of_nonneg_of_le
  · intro z
    exact inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)
  · intro z
    have hr := lattice_radius_ge_one z.property
    have h := Real.rpow_le_rpow_of_exponent_le hr (show -((d : ℝ) + 2) ≤ -(d : ℝ) - 1 by linarith)
    have he : -((d : ℝ) + 2) = -((d + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_neg_natCast, zpow_neg, zpow_natCast] at h
    exact h

/-- The cutoff-weighted critical kernel is summable for every real radius. -/
theorem summable_cutoff_energy (d : ℕ) (hd : 1 ≤ d) (r : ℝ) :
    Summable (fun z : {z : Site d // z ≠ 0} =>
      min 1 (radius (physical 1 z.val) ^ 2 / r ^ 2) *
        (radius (physical 1 z.val) ^ (d + 2))⁻¹) := by
  apply (summable_kernel d hd).of_nonneg_of_le
  · intro z
    exact mul_nonneg (le_min zero_le_one (div_nonneg (sq_nonneg _) (sq_nonneg _)))
      (inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))
  · intro z
    exact mul_le_of_le_one_left (inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _)) (min_le_left _ _)

/-- The cutoff energy is bounded by the total jump rate. -/
theorem cutoff_energy_le_total_rate (d : ℕ) (hd : 1 ≤ d) (r : ℝ) :
    (∑' z : {z : Site d // z ≠ 0},
      min 1 (radius (physical 1 z.val) ^ 2 / r ^ 2) *
        (radius (physical 1 z.val) ^ (d + 2))⁻¹) ≤
    ∑' z : {z : Site d // z ≠ 0}, (radius (physical 1 z.val) ^ (d + 2))⁻¹ := by
  exact (summable_cutoff_energy d hd r).tsum_le_tsum
    (fun z => mul_le_of_le_one_left (inv_nonneg.mpr (pow_nonneg (radius_nonneg _) _))
      (min_le_left _ _)) (summable_kernel d hd)

/-- The critical radial sum inside a lattice ball has logarithmic growth. -/
theorem critical_sum_le_log {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 1 ≤ r)
    (u : Finset (Site d)) (hu : ∀ z ∈ u, z ≠ 0 ∧ radius (physical 1 z) ≤ r) :
    ∑ z ∈ u, (radius (physical 1 z)) ^ (-(d : ℝ)) ≤
      shellConstant d * (1 + Real.log r) := by
  classical
  let g : Site d → ℕ := fun z => Nat.floor (radius (physical 1 z))
  have hsub : u.image g ⊆ Finset.Icc 1 (Nat.floor r) := by
    intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_Icc]
    exact ⟨(Nat.one_le_floor_iff _).mpr (lattice_radius_ge_one (hu z hz).1),
      Nat.floor_le_floor (hu z hz).2⟩
  have hs := shell_rpow_sum_le_fiber hd (Nat.cast_nonneg d) u (fun z hz => (hu z hz).1)
  have he : (d : ℝ) - 1 - d = -1 := by ring
  rw [he] at hs
  have hsum : ∑ n ∈ u.image g, (n : ℝ) ^ (-1 : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 (Nat.floor r), (n : ℝ) ^ (-1 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfloor : (1 : ℝ) ≤ (Nat.floor r : ℝ) := by
    exact_mod_cast (Nat.one_le_floor_iff r).mpr hr
  have hlog : Real.log (Nat.floor r : ℝ) ≤ Real.log r :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hh := sum_inv_Icc_le_one_add_log (Nat.floor r)
  exact hs.trans (mul_le_mul_of_nonneg_left (hsum.trans (by linarith)) (shellConstant_pos hd).le)

/-- The critical kernel outside a lattice ball has inverse-square decay. -/
theorem critical_tail_sum_le {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 1 ≤ r)
    (u : Finset (Site d)) (hu : ∀ z ∈ u, z ≠ 0 ∧ r ≤ radius (physical 1 z)) :
    ∑ z ∈ u, (radius (physical 1 z)) ^ (-((d : ℝ) + 2)) ≤
      shellConstant d * (24 * r ^ (-(2 : ℝ))) := by
  classical
  let g : Site d → ℕ := fun z => Nat.floor (radius (physical 1 z))
  have hs := shell_rpow_sum_le_fiber hd (show 0 ≤ (d : ℝ) + 2 by positivity) u
    (fun z hz => (hu z hz).1)
  have he : (d : ℝ) - 1 - ((d : ℝ) + 2) = -(2 : ℝ) - 1 := by ring
  rw [he] at hs
  have ht := tail_finset_bound (m := (2 : ℝ)) (R := r) (by norm_num) hr (u.image g)
    (by
      intro n hn
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
      exact Nat.floor_le_floor (hu z hz).2)
  have ht' : ∑ n ∈ u.image g, (n : ℝ) ^ (-(2 : ℝ) - 1) ≤
      24 * r ^ (-(2 : ℝ)) := by
    convert ht using 1
    norm_num
    ring
  exact hs.trans (mul_le_mul_of_nonneg_left ht' (shellConstant_pos hd).le)

private theorem kernel_inner {d : ℕ} {r a : ℝ} (ha : 0 < a) (hr : 0 < r) :
    min 1 (a ^ 2 / r ^ 2) * (a ^ (d + 2))⁻¹ ≤
      (r ^ 2)⁻¹ * a ^ (-(d : ℝ)) := by
  have h := mul_le_mul_of_nonneg_right (min_le_right 1 (a ^ 2 / r ^ 2))
    (inv_nonneg.mpr (pow_nonneg ha.le (d + 2)))
  have he : (a ^ 2 / r ^ 2) * (a ^ (d + 2))⁻¹ =
      (r ^ 2)⁻¹ * a ^ (-(d : ℝ)) := by
    rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast, pow_add]
    field_simp [ha.ne', hr.ne']
  exact h.trans_eq he

private theorem finite_energy_le {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 1 ≤ r)
    (u : Finset (Site d)) (hu : ∀ z ∈ u, z ≠ 0) :
    (∑ z ∈ u, min 1 (radius (physical 1 z) ^ 2 / r ^ 2) *
      (radius (physical 1 z) ^ (d + 2))⁻¹) ≤
    shellConstant d * ((1 + Real.log r + 24) * (r ^ 2)⁻¹) := by
  classical
  let s := u.filter (fun z => radius (physical 1 z) ≤ r)
  let t := u.filter (fun z => ¬ radius (physical 1 z) ≤ r)
  have hsplit := Finset.sum_filter_add_sum_filter_not u
    (fun z => radius (physical 1 z) ≤ r)
    (fun z => min 1 (radius (physical 1 z) ^ 2 / r ^ 2) *
      (radius (physical 1 z) ^ (d + 2))⁻¹)
  have hi := critical_sum_le_log hd hr s (by
    intro z hz
    exact ⟨hu z (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩)
  have ht := critical_tail_sum_le hd hr t (by
    intro z hz
    exact ⟨hu z (Finset.mem_filter.mp hz).1, le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hz).2)⟩)
  have hi' : ∑ z ∈ s, min 1 (radius (physical 1 z) ^ 2 / r ^ 2) *
      (radius (physical 1 z) ^ (d + 2))⁻¹ ≤
      (r ^ 2)⁻¹ * (shellConstant d * (1 + Real.log r)) := by
    calc
      _ ≤ ∑ z ∈ s, (r ^ 2)⁻¹ * (radius (physical 1 z)) ^ (-(d : ℝ)) := by
        apply Finset.sum_le_sum
        intro z hz
        exact kernel_inner (lt_of_lt_of_le zero_lt_one (lattice_radius_ge_one
          (hu z (Finset.mem_filter.mp hz).1))) (by linarith)
      _ = (r ^ 2)⁻¹ * ∑ z ∈ s, (radius (physical 1 z)) ^ (-(d : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (sq_nonneg r))
  have ht' : ∑ z ∈ t, min 1 (radius (physical 1 z) ^ 2 / r ^ 2) *
      (radius (physical 1 z) ^ (d + 2))⁻¹ ≤
      shellConstant d * (24 * (r ^ 2)⁻¹) := by
    have h : ∑ z ∈ t, min 1 (radius (physical 1 z) ^ 2 / r ^ 2) *
        (radius (physical 1 z) ^ (d + 2))⁻¹ ≤
        ∑ z ∈ t, (radius (physical 1 z)) ^ (-((d : ℝ) + 2)) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_of_le_one_left (inv_nonneg.mpr (pow_nonneg (radius_nonneg (physical 1 z)) (d + 2)))
        (min_le_left 1 (radius (physical 1 z) ^ 2 / r ^ 2))
      have he : -((d : ℝ) + 2) = -((d + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
      exact h
    have he : r ^ (-(2 : ℝ)) = (r ^ 2)⁻¹ := by
      rw [Real.rpow_neg (by linarith : 0 ≤ r)]
      exact congrArg Inv.inv (Real.rpow_natCast r 2)
    rw [he] at ht
    exact h.trans ht
  rw [← hsplit]
  change _ + _ ≤ _
  calc
    _ ≤ (r ^ 2)⁻¹ * (shellConstant d * (1 + Real.log r)) +
      shellConstant d * (24 * (r ^ 2)⁻¹) := add_le_add hi' ht'
    _ = _ := by ring

/-- The cutoff energy has logarithmic inverse-square decay at radii at least one. -/
theorem cutoff_energy_le_log {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 1 ≤ r) :
    (∑' z : {z : Site d // z ≠ 0},
      min 1 (radius (physical 1 z.val) ^ 2 / r ^ 2) *
        (radius (physical 1 z.val) ^ (d + 2))⁻¹) ≤
    (shellConstant d * (1 + 25 / Real.log 3)) * Real.log (2 + r) / r ^ 2 := by
  have hsum : (∑' z : {z : Site d // z ≠ 0},
      min 1 (radius (physical 1 z.val) ^ 2 / r ^ 2) *
        (radius (physical 1 z.val) ^ (d + 2))⁻¹) ≤
      shellConstant d * ((1 + Real.log r + 24) * (r ^ 2)⁻¹) :=
    (summable_cutoff_energy d hd r).tsum_le_of_sum_le (by
    intro u
    have h := finite_energy_le hd hr (u.image Subtype.val) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      exact w.property)
    rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)] at h
    exact h)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl : Real.log 3 ≤ Real.log (2 + r) := Real.log_le_log (by norm_num) (by linarith)
  have hlr : Real.log r ≤ Real.log (2 + r) := Real.log_le_log (by linarith) (by linarith)
  have hlog : 1 + Real.log r + 24 ≤ (1 + 25 / Real.log 3) * Real.log (2 + r) := by
    have hdiv : 25 ≤ (25 / Real.log 3) * Real.log (2 + r) := by
      have := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ 25 / Real.log 3 by positivity)
      have : (25 / Real.log 3) * Real.log 3 = 25 := by field_simp
      linarith
    nlinarith
  calc
    _ ≤ shellConstant d * ((1 + Real.log r + 24) * (r ^ 2)⁻¹) := hsum
    _ ≤ shellConstant d * (((1 + 25 / Real.log 3) * Real.log (2 + r)) * (r ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr (sq_nonneg r)))
        (shellConstant_pos hd).le
    _ = _ := by ring

end LatticeProb.Analysis.CriticalCutoffEnergy

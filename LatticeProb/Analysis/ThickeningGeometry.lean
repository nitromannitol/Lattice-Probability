import Mathlib
import LatticeProb.Analysis.ShellGeometry

/-!
# Thickenings of a set and the distance function near a level

Facts about the `δ`-thickening `E + B_δ` of a set `E` in the complex plane, and about the distance function
`infDist · E` near a point `p` with `infDist p E = r / 2`:

* every `x ∈ (0, 1]` has a dyadic scale `(1/2)^n ∈ (x/2, x]`, and every point of `ℂ` lies within `δ / 100` of the
  grid `(δ / 100) ℤ²`;
* a point of the frontier of `E + B_δ` is at distance exactly `δ` from `E`;
* if `‖w - p‖ < 3 r / 8`, then `r / 8 < infDist w E < 7 r / 8`; hence `w` lies in the thickening `E + B_r`, outside
  the closure of `E`, and at distance more than `r / 8` from the frontier of `E + B_r` (potential theory of the
  distance function, Armitage-Gardiner).
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

namespace ThickeningGeometry

/-- Dyadic scales: for `x ∈ (0, 1]` there is `n : ℕ` with `x / 2 < (1 / 2) ^ n ≤ x`. -/
theorem exists_half_pow_mem {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ∃ n : ℕ, x / 2 < (1 / 2 : ℝ) ^ n ∧ (1 / 2 : ℝ) ^ n ≤ x := by
  classical
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]
    linarith
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [not_le] at hmin
    rw [hk, pow_succ]
    linarith

/-- Every point of `ℂ` lies within `δ / 100` of the grid `(δ / 100) ℤ²`, for `δ > 0`. -/
theorem exists_grid_near {δ : ℝ} (hδ : 0 < δ) (p : ℂ) :
    ∃ m n : ℤ, ‖p - ((δ / 100 : ℝ) : ℂ) * (m + n * Complex.I)‖ ≤ δ / 100 := by
  set h : ℝ := δ / 100
  have hpos : 0 < h := by positivity
  refine ⟨round (p.re / h), round (p.im / h), ?_⟩
  have hre : |p.re / h - round (p.re / h)| ≤ 1 / 2 := abs_sub_round _
  have him : |p.im / h - round (p.im / h)| ≤ 1 / 2 := abs_sub_round _
  set w := p - (h : ℂ) * (round (p.re / h) + round (p.im / h) * Complex.I)
  have hwre : w.re = h * (p.re / h - round (p.re / h)) := by
    have : w.re = p.re - h * round (p.re / h) := by simp [w]
    rw [this]
    field_simp
  have hwim : w.im = h * (p.im / h - round (p.im / h)) := by
    have : w.im = p.im - h * round (p.im / h) := by simp [w]
    rw [this]
    field_simp
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ = h * |p.re / h - round (p.re / h)| + h * |p.im / h - round (p.im / h)| := by
        rw [hwre, hwim, abs_mul, abs_mul, abs_of_pos hpos]
    _ ≤ h * (1 / 2) + h * (1 / 2) := by gcongr
    _ = h := by ring

/-- A point of the frontier of the thickening `E + B_δ` is at distance exactly `δ` from `E`. -/
theorem infDist_eq_of_mem_frontier_thickening {E : Set ℂ} {δ : ℝ} (hδ : 0 ≤ δ) {p : ℂ}
    (hp : p ∈ frontier (thickening δ E)) : infDist p E = δ := by
  have h := frontier_thickening_subset E hp
  simp only [mem_ofPred_eq] at h
  unfold infDist
  rw [h, ENNReal.toReal_ofReal hδ]

/-- If `infDist p E = r / 2` and `‖w - p‖ < 3 r / 8`, then `r / 8 < infDist w E`. -/
theorem lt_infDist_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : r / 8 < infDist w E := by
  have h := LatticeProb.ShellGeometry.abs_infDist_sub_infDist_le E p w
  rw [hp, dist_eq_norm, norm_sub_rev] at h
  linarith [(abs_le.1 h).2]

/-- If `infDist p E = r / 2` and `‖w - p‖ < 3 r / 8`, then `infDist w E < 7 r / 8`. -/
theorem infDist_lt_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : infDist w E < 7 * r / 8 := by
  have h := LatticeProb.ShellGeometry.abs_infDist_sub_infDist_le E p w
  rw [hp, dist_eq_norm, norm_sub_rev] at h
  linarith [(abs_le.1 h).1]

/-- Under the hypotheses of `lt_infDist_of_near`, `w` is not in the closure of `E`. -/
theorem notMem_closure_of_near {E : Set ℂ} {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : w ∉ closure E := fun h => by
  have h1 := infDist_zero_of_mem_closure h
  have h2 : r / 8 < infDist w E := lt_infDist_of_near hp hw
  have h3 := norm_nonneg (w - p)
  linarith

/-- Under the hypotheses of `lt_infDist_of_near`, `w` lies in the thickening `E + B_r` of a nonempty set `E`. -/
theorem mem_thickening_of_near {E : Set ℂ} (hE : E.Nonempty) {p w : ℂ} {r : ℝ} (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) : w ∈ thickening r E := by
  rw [mem_thickening_iff_infDist_lt hE]
  have h := infDist_lt_of_near hp hw
  have h0 : 0 ≤ ‖w - p‖ := norm_nonneg _
  linarith

/-- Under the hypotheses of `lt_infDist_of_near`, every point `w₁` of the frontier of `E + B_r` is at distance more
than `r / 8` from `w`. -/
theorem lt_dist_of_mem_frontier {E : Set ℂ} {p w w₁ : ℂ} {r : ℝ} (hr : 0 ≤ r) (hp : infDist p E = r / 2)
    (hw : ‖w - p‖ < 3 * r / 8) (hw₁ : w₁ ∈ frontier (thickening r E)) : r / 8 < dist w₁ w := by
  have h1 := infDist_eq_of_mem_frontier_thickening hr hw₁
  have h2 := infDist_lt_of_near hp hw
  have h3 := (abs_le.1 (LatticeProb.ShellGeometry.abs_infDist_sub_infDist_le E w₁ w)).2
  linarith

end ThickeningGeometry

end LatticeProb

import LatticeProb.Analysis.PlanarPackingInverseSquare

/-!
# Inverse-square sums over fat planar cells

A *fat cell* is a bounded measurable set `H ⊆ ℂ` containing a disc `B_r(c)`. If the cell is far
from a point `u` compared with its size, `diam H ≤ dist(u, H)`, then every `w ∈ H` satisfies
`|w - u| ≤ dist(u, H) + diam H ≤ 2 dist(u, H)`, and averaging over `H` (whose area is at least
`π r²`) gives
`r² / dist(u, H)² ≤ (4 / π) ∫_H |w - u|⁻² dw`.
Summing over pairwise almost disjoint cells inside the closed disc `|w - u| ≤ R`, almost disjoint
from the disc `|w - u| < r₀`, and using `∫_{r₀ ≤ |w - u| ≤ R} |w - u|⁻² dw = 2π log(R / r₀)`, gives
`∑ r_i² / dist(u, H_i)² ≤ 8 log(R / r₀)`.

This is the comparison of the energy of a unit flow over a planar cell configuration with a
logarithmic integral, used to bound effective resistances of cell graphs in the plane.

## Main results

* `norm_sub_le_two_mul_infDist`: `|w - u| ≤ 2 dist(u, H)` for `w ∈ H` when `diam H ≤ dist(u, H)`.
* `ofReal_sq_div_sq_infDist_le_lintegral`: the single-cell comparison.
* `sum_sq_div_sq_infDist_le`: the summed bound `∑ r_i² / dist(u, H_i)² ≤ 8 log(R / r₀)`.
-/

open MeasureTheory Metric Set Real Function
open scoped ENNReal

namespace LatticeProb

/-- A point of a bounded set `H` lies within `2 dist(u, H)` of `u` when `diam H ≤ dist(u, H)`. -/
theorem norm_sub_le_two_mul_infDist {H : Set ℂ} {u w : ℂ} (hb : Bornology.IsBounded H)
    (hw : w ∈ H) (hdiam : diam H ≤ infDist u H) : ‖w - u‖ ≤ 2 * infDist u H := by
  have h := dist_le_infDist_add_diam (x := u) hb hw
  rw [dist_comm, dist_eq_norm] at h
  linarith

/-- **Single fat cell.** If `B_r(c) ⊆ H`, `H` is bounded and measurable, and
`0 < dist(u, H)` with `diam H ≤ dist(u, H)`, then
`r² / dist(u, H)² ≤ (4 / π) ∫_H |w - u|⁻² dw`. -/
theorem ofReal_sq_div_sq_infDist_le_lintegral {H : Set ℂ} {c u : ℂ} {r : ℝ}
    (hb : Bornology.IsBounded H) (hr : 0 ≤ r) (hball : ball c r ⊆ H)
    (hpos : 0 < infDist u H) (hdiam : diam H ≤ infDist u H) :
    ENNReal.ofReal (r ^ 2 / infDist u H ^ 2)
      ≤ ENNReal.ofReal (4 / π) * ∫⁻ w in H, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
  have hlow : ∀ w ∈ H,
      ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) ≤ ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
    intro w hw
    apply ENNReal.ofReal_le_ofReal
    have h1 := norm_sub_le_two_mul_infDist hb hw hdiam
    have hne : 0 < ‖w - u‖ := by
      have := infDist_le_dist_of_mem (x := u) hw
      rw [dist_comm, dist_eq_norm] at this
      linarith
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    nlinarith
  have hmeas : Measurable fun w : ℂ => ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by fun_prop
  have hpi : ((NNReal.pi : ℝ≥0∞)) = ENNReal.ofReal π := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hd0 : infDist u H ≠ 0 := hpos.ne'
  calc ENNReal.ofReal (r ^ 2 / infDist u H ^ 2)
      = ENNReal.ofReal (4 / π) *
          (ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) * (ENNReal.ofReal r ^ 2 * NNReal.pi)) := by
        rw [hpi, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (4 / π) * (ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) * volume H) := by
        gcongr
        rw [← Complex.volume_ball c r]
        exact measure_mono hball
    _ = ENNReal.ofReal (4 / π) * ∫⁻ _w in H, ENNReal.ofReal ((4 * infDist u H ^ 2)⁻¹) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (4 / π) * ∫⁻ w in H, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
        exact mul_le_mul' le_rfl (setLIntegral_mono hmeas hlow)

/-- **Inverse-square sum over fat cells.** Let `H_i` (`i ∈ s`) be pairwise almost disjoint bounded
measurable sets in the closed disc `closedBall u R`, each almost disjoint from `ball u r₀`, each
containing a disc `B_{ρ_i}(c_i)` and far from `u` compared with its size
(`0 < dist(u, H_i)`, `diam H_i ≤ dist(u, H_i)`). Then
`∑ ρ_i² / dist(u, H_i)² ≤ 8 log(R / r₀)`. -/
theorem sum_sq_div_sq_infDist_le {ι : Type*} {s : Finset ι} {H : ι → Set ℂ} {c : ι → ℂ}
    {ρ : ι → ℝ} {u : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hd : (s : Set ι).Pairwise (AEDisjoint volume on H))
    (hHm : ∀ i ∈ s, MeasurableSet (H i)) (hb : ∀ i ∈ s, Bornology.IsBounded (H i))
    (hρ : ∀ i ∈ s, 0 ≤ ρ i) (hball : ∀ i ∈ s, ball (c i) (ρ i) ⊆ H i)
    (hpos : ∀ i ∈ s, 0 < infDist u (H i)) (hdiam : ∀ i ∈ s, diam (H i) ≤ infDist u (H i))
    (hsub : ∀ i ∈ s, H i ⊆ closedBall u R)
    (hout : ∀ i ∈ s, AEDisjoint volume (H i) (ball u r)) :
    ∑ i ∈ s, ρ i ^ 2 / infDist u (H i) ^ 2 ≤ 8 * Real.log (R / r) := by
  have hlog : 0 ≤ Real.log (R / r) := Real.log_nonneg ((one_le_div hr).2 hrR)
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  have hd' : (s : Set ι).Pairwise (AEDisjoint volume on fun i => H i \ ball u r) :=
    fun i hi j hj hij => (hd hi hj hij).mono sdiff_subset sdiff_subset
  calc ∑ i ∈ s, ENNReal.ofReal (ρ i ^ 2 / infDist u (H i) ^ 2)
      ≤ ∑ i ∈ s, ENNReal.ofReal (4 / π) *
          ∫⁻ w in H i \ ball u r, ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
        gcongr with i hi
        rw [setLIntegral_congr (hout i hi).sdiff_ae_eq_left]
        exact ofReal_sq_div_sq_infDist_le_lintegral (hb i hi) (hρ i hi) (hball i hi)
          (hpos i hi) (hdiam i hi)
    _ = ENNReal.ofReal (4 / π) *
          ∫⁻ w in ⋃ i ∈ s, (H i \ ball u r), ENNReal.ofReal ((‖w - u‖ ^ 2)⁻¹) := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset₀ hd'
          (fun i hi => ((hHm i hi).diff measurableSet_ball).nullMeasurableSet)]
    _ ≤ ENNReal.ofReal (4 / π) * ENNReal.ofReal (2 * π * Real.log (R / r)) := by
        gcongr
        refine lintegral_inv_sq_norm_sub_le_of_subset_annulus u hr hrR ?_
        intro w hw
        simp only [mem_iUnion] at hw
        obtain ⟨i, hi, hwi⟩ := hw
        exact ⟨hsub i hi hwi.1, hwi.2⟩
    _ = ENNReal.ofReal (8 * Real.log (R / r)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

end LatticeProb
